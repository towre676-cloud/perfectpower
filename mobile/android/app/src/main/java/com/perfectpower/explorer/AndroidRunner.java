package com.perfectpower.explorer;
import android.content.*;
import android.os.*;
import org.json.JSONObject;
import java.nio.file.*;
import java.util.Set;
import java.util.concurrent.*;

public final class AndroidRunner {
    private final Context context;
    private final Set<String> cancelled=ConcurrentHashMap.newKeySet();
    private volatile Messenger active;
    private volatile String activeId;
    private volatile CountDownLatch current;
    public AndroidRunner(Context context) { this.context=context.getApplicationContext(); }
    public void cancel(String id) {
        cancelled.add(id);
        if (id.equals(activeId)) { stopWorker(); CountDownLatch latch=current;if(latch!=null)latch.countDown(); }
    }
    private void stopWorker() { Messenger worker=active;if(worker!=null)try{worker.send(Message.obtain(null,2));}catch(RemoteException ignored){} }
    public void close() { stopWorker();context.stopService(new Intent(context,EngineService.class)); }
    public synchronized String execute(String payload,int timeout) throws Exception {
        JSONObject request=new JSONObject(payload);String id=request.getString("id");
        if(cancelled.remove(id))return "{\"status\":\"cancelled\",\"error\":\"Cancelled before execution.\"}";
        Path path=Path.of(request.getString("folder"),"request.json");Files.write(path,payload.getBytes(java.nio.charset.StandardCharsets.UTF_8));
        CountDownLatch connected=new CountDownLatch(1),done=new CountDownLatch(1),dead=new CountDownLatch(1);String[] answer={null};
        Messenger receiver=new Messenger(new Handler(Looper.getMainLooper()){@Override public void handleMessage(Message message){answer[0]=message.getData().getString("result");done.countDown();}});
        ServiceConnection connection=new ServiceConnection(){
            @Override public void onServiceConnected(ComponentName name,IBinder binder){try{binder.linkToDeath(()->dead.countDown(),0);}catch(RemoteException error){dead.countDown();}active=new Messenger(binder);connected.countDown();}
            @Override public void onServiceDisconnected(ComponentName name){done.countDown();}
            @Override public void onBindingDied(ComponentName name){done.countDown();connected.countDown();}
        };
        activeId=id;current=done;
        boolean portfolio="portfolio".equals(request.getJSONObject("body").optString("kind"));
        if(portfolio)context.startService(new Intent(context,EngineService.class));
        boolean bound=context.bindService(new Intent(context,EngineService.class),connection,Context.BIND_AUTO_CREATE);
        try {
            if(!bound||!connected.await(30,TimeUnit.SECONDS)||active==null)throw new IllegalStateException("Android could not start the computation process.");
            if(cancelled.contains(id))return "{\"status\":\"cancelled\"}";
            Message message=Message.obtain(null,1);Bundle data=new Bundle();data.putString("path",path.toString());message.setData(data);message.replyTo=receiver;active.send(message);
            boolean completed=done.await(timeout,TimeUnit.SECONDS);
            if(cancelled.remove(id))return "{\"status\":\"cancelled\",\"error\":\"Computation stopped. No complete answer is inferred.\"}";
            if(!completed)return "{\"status\":\"timeout\",\"error\":\"Time limit reached. Computation process stopped; no complete answer is inferred.\"}";
            return answer[0]!=null?answer[0]:"{\"status\":\"failed\",\"error\":\"Android stopped the computation process, possibly because of memory pressure.\"}";
        } finally {
            if(!portfolio||answer[0]==null||cancelled.contains(id)){stopWorker();context.stopService(new Intent(context,EngineService.class));dead.await(3,TimeUnit.SECONDS);}
            if(bound)context.unbindService(connection);active=null;activeId=null;current=null;
        }
    }
}
