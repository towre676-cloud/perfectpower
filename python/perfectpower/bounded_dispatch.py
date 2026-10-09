"""Serial persistent catalogue in a terminable process, independent of HTTP threads."""
import multiprocessing
import threading
import time
from .catalogue import encoded


class QueryDeadline(TimeoutError):
    pass


class QueryFailure(Exception):
    def __init__(self,name,message):
        self.name=name;self.message=message
        super().__init__(message)


def _worker(connection, database):
    from .catalogue import Catalogue
    from .query_service import dispatch
    try:
        with Catalogue(database) as catalogue:
            while True:
                request=connection.recv()
                if request is None:break
                try:
                    value=dispatch(catalogue,request)
                    # Serialize inside the process so expensive output cannot block HTTP.
                    connection.send(('ok',encoded(value)))
                except Exception as error:
                    connection.send(('error',type(error).__name__,str(error)))
    except (EOFError,BrokenPipeError):
        pass
    finally:connection.close()


class BoundedDispatcher:
    def __init__(self,database,timeout=30):
        if type(timeout) not in (int,float) or not 0<timeout<=600:
            raise ValueError('query timeout must be positive and at most 600 seconds')
        self.database=str(database);self.timeout=timeout
        self.lock=threading.Lock();self.process=None;self.connection=None;self.closed=False

    def _stop(self):
        if self.process is not None:
            if self.process.is_alive():self.process.terminate()
            self.process.join(timeout=1)
            if self.process.is_alive():self.process.kill();self.process.join(timeout=1)
            self.process.close();self.process=None
        if self.connection is not None:self.connection.close();self.connection=None

    def _start(self):
        context=multiprocessing.get_context('spawn')
        parent,child=context.Pipe()
        process=context.Process(target=_worker,args=(child,self.database),daemon=True)
        try:process.start()
        except BaseException:parent.close();child.close();raise
        child.close();self.process=process;self.connection=parent

    def call(self,request):
        start=time.monotonic()
        if not self.lock.acquire(timeout=self.timeout):
            raise QueryDeadline('query queue deadline exceeded; request was not executed')
        try:
            if self.closed:raise RuntimeError('dispatcher closed')
            if self.process is None:self._start()
            remaining=self.timeout-(time.monotonic()-start)
            if remaining<=0:raise QueryDeadline('query queue deadline exceeded; request was not executed')
            self.connection.send(request)
            if not self.connection.poll(remaining):
                self._stop()
                raise QueryDeadline('query deadline exceeded; worker stopped; inspect persisted state before retrying a mutation')
            message=self.connection.recv()
            if message[0]=='ok':return message[1]
            raise QueryFailure(message[1],message[2])
        except QueryDeadline:
            raise
        except (EOFError,BrokenPipeError,OSError) as error:
            self._stop();raise RuntimeError('query worker failed') from error
        finally:self.lock.release()

    def close(self):
        with self.lock:
            self.closed=True;self._stop()
