package com.perfectpower.explorer;
import android.test.ActivityInstrumentationTestCase2;
import android.webkit.WebView;
import org.json.*;
import java.util.concurrent.*;

public class ExplorerDeviceTest extends ActivityInstrumentationTestCase2<MainActivity> {
    public ExplorerDeviceTest(){super(MainActivity.class);}
    private MainActivity activity;
    private String js(String code)throws Exception{
        CountDownLatch latch=new CountDownLatch(1);String[] value={null};
        getInstrumentation().runOnMainSync(()->activity.getExplorerView().evaluateJavascript(code,result->{value[0]=result;latch.countDown();}));
        assertTrue("JavaScript response",latch.await(15,TimeUnit.SECONDS));return value[0];
    }
    private JSONObject request(String body)throws Exception{
        js("window.__qa=null; fetch('/api/run',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify("+body+")}).then(r=>r.json()).then(v=>window.__qa=v)");
        JSONObject submit=pollObject("window.__qa",30);String id=submit.getString("id");
        for(int i=0;i<600;i++){
            js("window.__qa=null;fetch('/api/job?id="+id+"').then(r=>r.json()).then(v=>window.__qa=v)");
            JSONObject job=pollObject("window.__qa",20);
            if(!job.getString("status").equals("running"))return job;
            Thread.sleep(300);
        }throw new AssertionError("Run did not finish");
    }
    private JSONObject pollObject(String expression,int seconds)throws Exception{
        for(int i=0;i<seconds*5;i++){String result=js(expression);if(result!=null&&!result.equals("null"))return new JSONObject(result);Thread.sleep(200);}throw new AssertionError("No JSON response: "+expression);
    }
    public void testCompleteExplorerOnAndroid()throws Exception{
        activity=getActivity();
        for(int i=0;i<900&&activity.getExplorerView()==null;i++)Thread.sleep(200);
        assertNotNull("Complete startup",activity.getExplorerView());
        for(int i=0;i<600;i++){String value=js("document.querySelectorAll('#nav button').length");if("7".equals(value))break;Thread.sleep(200);}
        assertEquals("All navigation workspaces","7",js("document.querySelectorAll('#nav button').length"));
        assertEquals("No phone horizontal overflow","true",js("document.documentElement.scrollWidth<=innerWidth+1"));
        js("window.__qa=null;fetch('/api/catalog').then(r=>r.json()).then(v=>window.__qa={commands:Object.keys(v.commands).length,files:v.mobile.original_file_count})");
        JSONObject catalog=pollObject("window.__qa",30);assertEquals(145,catalog.getInt("commands"));assertEquals(7501,catalog.getInt("files"));
        JSONObject scan=request("{kind:'scan',spec:{coeff:['-2','0','0','1'],d:2,lo:-20,hi:20}}");
        assertEquals(scan.toString(),"complete",scan.getString("status"));assertEquals(2,scan.getJSONObject("result").getInt("count"));
        JSONObject cnf=request("{kind:'command',args:['model-count','examples/desktop_explorer/starter.cnf','--timeout','10'],timeout:40}");
        assertEquals(cnf.toString(),"complete",cnf.getString("status"));assertEquals("4",cnf.getJSONObject("result").getString("count"));
        String[][] commands={
            {"solve","--expr","(5*n - 7)**3 - 2","--domain","pos"},
            {"exact-solve","--coeff","[-199,1,1,1,1]"},
            {"plan","examples/planning/petersen_6.json"},
            {"graph","flow","examples/graph_methods/flow.json"},
            {"geometry-foundations","triangulate","examples/belyaev_geometry/triangulate.json"},
            {"euclid","pell","examples/euclid_methods/pell.json"},
            {"arithmetic-series","compile","examples/arithmetic_series/pell.json"}
        };
        for(String[] args:commands){JSONObject body=new JSONObject().put("kind","command").put("args",new JSONArray(args)).put("timeout",60);JSONObject job=request(body.toString());assertEquals(job.toString(),"complete",job.getString("status"));assertEquals(0,job.getInt("exit_code"));}
        // Verify isolated worker cancellation with a real retained repository script.
        js("window.__qa=null;fetch('/api/run',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({kind:'command',args:['plan','examples/planning/petersen_50_population.json'],timeout:60})}).then(r=>r.json()).then(v=>window.__qa=v)");
        String id=pollObject("window.__qa",30).getString("id");
        js("fetch('/api/cancel',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({id:'"+id+"'})})");
        Thread.sleep(1500);
        js("window.__qa=null;fetch('/api/job?id="+id+"').then(r=>r.json()).then(v=>window.__qa=v)");
        assertEquals("cancelled",pollObject("window.__qa",20).getString("status"));
        JSONObject after=request("{kind:'scan',spec:{coeff:['-2','0','0','1'],d:2,lo:0,hi:5}}");assertEquals("complete",after.getString("status"));
        js("location.hash='settings'");Thread.sleep(500);assertEquals("true",js("document.body.textContent.includes('coverage report')"));
        js("location.hash='home'");
    }
}
