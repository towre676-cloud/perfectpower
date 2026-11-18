#!/usr/bin/env python3
"""Execute all submission cells in a fresh Python process; capture only aggregates.

This avoids opening Jupyter sockets. It is not a Kaggle-hosted kernel execution.
"""
import argparse
import base64
import contextlib
import io
import json
import os
from pathlib import Path
import nbformat


def verify(notebook, output, figures):
    os.environ['BDB_SUBMISSION_MODE']='receipts'
    os.environ['BDB_SUBMISSION_OUTPUT']=str(figures.resolve())
    n=nbformat.read(notebook,as_version=4);nbformat.validate(n);scope={'__name__':'__submission_cell_replay__'};count=0
    for i,c in enumerate(n.cells):
        if c.cell_type!='code':continue
        count+=1;captured=[]
        def capture_display(obj):
            data=getattr(obj,'data',None)
            if isinstance(data,bytes):captured.append(nbformat.v4.new_output('display_data',data={'image/png':base64.b64encode(data).decode()},metadata={}))
            else:captured.append(nbformat.v4.new_output('display_data',data={'text/plain':str(obj)},metadata={}))
        stream=io.StringIO()
        with contextlib.redirect_stdout(stream),contextlib.redirect_stderr(stream):exec(compile(''.join(c.source),f'{notebook}:cell{i}','exec'),scope)
        scope['display']=capture_display
        c.execution_count=count;c.outputs=[]
        if stream.getvalue():c.outputs.append(nbformat.v4.new_output('stream',name='stdout',text=stream.getvalue()))
        c.outputs.extend(captured)
    figure_count=sum('image/png' in o.get('data',{}) for c in n.cells if c.cell_type=='code' for o in c.outputs)
    if figure_count!=4:raise ValueError('Expected exactly four displayed figures')
    n.metadata['execution_method']='Fresh Python process, sequential cells; not a Jupyter/Kaggle kernel run'
    output.write_text(nbformat.writes(n));print(json.dumps({'code_cells_executed':count,'figures':figure_count,'mode':'receipts','raw_tracking_executed':False,'execution_method':n.metadata['execution_method']}))


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    for key in ('notebook','output','figures'):p.add_argument('--'+key,type=Path,required=True)
    a=p.parse_args();verify(a.notebook,a.output,a.figures)
