package com.perfectpower.explorer;
import android.app.*;
import android.content.*;
import android.graphics.Color;
import android.net.Uri;
import android.os.*;
import android.webkit.*;
import android.view.*;
import android.widget.*;
import com.chaquo.python.Python;
import com.chaquo.python.android.AndroidPlatform;
import java.io.*;
import java.net.*;
import java.nio.file.*;
import java.security.*;
import java.util.zip.*;
import org.json.*;

public class MainActivity extends Activity {
    private WebView web;
    private TextView status;
    private String localOrigin,pendingUrl,pendingCookie,sessionUrl;
    private boolean engineReady;
    WebView getExplorerView(){return web;}
    @Override public void onCreate(Bundle saved){
        super.onCreate(saved);getWindow().setStatusBarColor(Color.rgb(20,34,53));getWindow().setNavigationBarColor(Color.rgb(20,34,53));
        LinearLayout splash=new LinearLayout(this);splash.setOrientation(LinearLayout.VERTICAL);splash.setGravity(Gravity.CENTER);splash.setBackgroundColor(Color.rgb(20,34,53));
        ImageView logo=new ImageView(this);logo.setImageResource(com.perfectpower.explorer.R.drawable.icon);splash.addView(logo,new LinearLayout.LayoutParams(180,180));
        TextView title=new TextView(this);title.setText("PerfectPower\nEXPLORER");title.setTextColor(Color.rgb(235,225,198));title.setTextSize(28);title.setGravity(Gravity.CENTER);splash.addView(title);
        status=new TextView(this);status.setText("Preparing your complete observatory…\nFirst launch verifies every included file.");status.setTextColor(Color.rgb(180,203,199));status.setTextSize(15);status.setGravity(Gravity.CENTER);status.setPadding(35,35,35,35);splash.addView(status);setContentView(splash);
        new Thread(()->{
            try{
                String fingerprint=readAsset("repository.sha256").trim();File root=new File(getFilesDir(),"repository-"+fingerprint.substring(0,12));
                if(!new File(root,".ready").isFile())extract(root,fingerprint);
                if(!Python.isStarted())Python.start(new AndroidPlatform(this));
                String abi=android.os.Build.SUPPORTED_ABIS[0];
                String url=Python.getInstance().getModule("mobile_runtime").callAttr("start",root.toString(),new File(getFilesDir(),"saved-runs").toString(),new AndroidRunner(this),abi).toString();
                runOnUiThread(()->open(url));
            }catch(Throwable error){runOnUiThread(()->status.setText("Unable to open the explorer.\n"+error+"\nClose and reopen to retry. No saved runs are deleted."));}
        },"PerfectPower startup").start();
    }
    private String readAsset(String name)throws IOException {try(InputStream in=getAssets().open(name)){return new String(in.readAllBytes(),java.nio.charset.StandardCharsets.UTF_8);}}
    private void extract(File root,String expected)throws Exception{
        MessageDigest hash=MessageDigest.getInstance("SHA-256");try(InputStream in=getAssets().open("repository.zip")){byte[] b=new byte[65536];int n;while((n=in.read(b))!=-1)hash.update(b,0,n);}
        if(!hex(hash.digest()).equals(expected))throw new IOException("Repository archive checksum mismatch.");
        JSONObject manifest=new JSONObject(readAsset("original-files.json"));JSONObject records=manifest.getJSONObject("files");int count=0;
        root.mkdirs();
        try(ZipInputStream zip=new ZipInputStream(getAssets().open("repository.zip"))){ZipEntry entry;byte[] b=new byte[65536];while((entry=zip.getNextEntry())!=null){
            File file=new File(root,entry.getName());if(!file.getCanonicalPath().startsWith(root.getCanonicalPath()+File.separator))throw new IOException("Unsafe archive path.");
            if(entry.isDirectory()){file.mkdirs();continue;}file.getParentFile().mkdirs();hash.reset();
            try(OutputStream out=new FileOutputStream(file)){int n;while((n=zip.read(b))!=-1){out.write(b,0,n);hash.update(b,0,n);}}
            if(records.has(entry.getName())){if(!hex(hash.digest()).equals(records.getString(entry.getName())))throw new IOException("File checksum mismatch: "+entry.getName());count++;}
            if(count%150==0){final int done=count;runOnUiThread(()->status.setText("Verifying the complete repository…\n"+done+" / "+records.length()+" source and data files"));}
        }}
        if(count!=records.length())throw new IOException("Incomplete repository: "+count+" of "+records.length());
        Files.write(new File(root,".ready").toPath(),expected.getBytes(java.nio.charset.StandardCharsets.UTF_8));
    }
    private static String hex(byte[] bytes){StringBuilder s=new StringBuilder();for(byte b:bytes)s.append(String.format("%02x",b&255));return s.toString();}
    private void open(String url){
        sessionUrl=url;
        Uri uri=Uri.parse(url);localOrigin="http://127.0.0.1:"+uri.getPort();
        web=new WebView(this);web.setBackgroundColor(Color.rgb(245,246,243));web.getSettings().setJavaScriptEnabled(true);web.getSettings().setDomStorageEnabled(true);web.getSettings().setAllowFileAccess(false);web.getSettings().setAllowContentAccess(false);web.getSettings().setSupportMultipleWindows(false);web.getSettings().setMediaPlaybackRequiresUserGesture(true);
        android.webkit.CookieManager.getInstance().setAcceptCookie(true);
        web.setWebViewClient(new WebViewClient(){
            @Override public boolean shouldOverrideUrlLoading(WebView view,WebResourceRequest request){
                String target=request.getUrl().toString();if(target.startsWith(localOrigin+"/")||target.equals(localOrigin))return false;
                if(request.isForMainFrame()&&("https".equals(request.getUrl().getScheme())||"http".equals(request.getUrl().getScheme())))try{startActivity(new Intent(Intent.ACTION_VIEW,request.getUrl()));}catch(ActivityNotFoundException ignored){}
                return true;
            }
            @Override public void onPageFinished(WebView view,String target){engineReady=true;}
        });
        web.setWebChromeClient(new WebChromeClient());
        web.setDownloadListener((target,userAgent,contentDisposition,mime,length)->{
            if(!target.startsWith(localOrigin+"/")){Toast.makeText(this,"Open external downloads in your browser.",Toast.LENGTH_LONG).show();return;}
            pendingUrl=target;pendingCookie=android.webkit.CookieManager.getInstance().getCookie(target);
            String name=Uri.parse(target).getLastPathSegment();if(name==null)name="PerfectPower-export.json";
            Intent intent=new Intent(Intent.ACTION_CREATE_DOCUMENT);intent.addCategory(Intent.CATEGORY_OPENABLE);intent.setType(mime!=null&&!mime.isEmpty()?mime:"application/octet-stream");intent.putExtra(Intent.EXTRA_TITLE,name);startActivityForResult(intent,41);
        });
        setContentView(web);web.setOnApplyWindowInsetsListener((view,insets)->{view.setPadding(insets.getSystemWindowInsetLeft(),insets.getSystemWindowInsetTop(),insets.getSystemWindowInsetRight(),insets.getSystemWindowInsetBottom());return insets.consumeSystemWindowInsets();});web.loadUrl(url);
    }
    @Override protected void onActivityResult(int request,int result,Intent data){super.onActivityResult(request,result,data);if(request!=41||result!=RESULT_OK||data==null)return;
        final String url=pendingUrl,cookie=pendingCookie;final Uri destination=data.getData();
        new Thread(()->{try{HttpURLConnection connection=(HttpURLConnection)new URL(url).openConnection();connection.setInstanceFollowRedirects(false);if(cookie!=null)connection.setRequestProperty("Cookie",cookie);if(connection.getResponseCode()!=200)throw new IOException("Export returned HTTP "+connection.getResponseCode());try(InputStream in=connection.getInputStream();OutputStream out=getContentResolver().openOutputStream(destination)){in.transferTo(out);}connection.disconnect();runOnUiThread(()->Toast.makeText(this,"Complete file exported.",Toast.LENGTH_LONG).show());}catch(Exception error){runOnUiThread(()->Toast.makeText(this,"Export failed: "+error.getMessage(),Toast.LENGTH_LONG).show());}},"PerfectPower export").start();
    }
    @Override public void onBackPressed(){if(web!=null&&web.canGoBack())web.goBack();else if(engineReady)new AlertDialog.Builder(this).setMessage("Close PerfectPower Explorer? Saved runs remain on your phone.").setPositiveButton("Close",(d,w)->finish()).setNegativeButton("Stay",null).show();else super.onBackPressed();}
    @Override protected void onDestroy(){if(web!=null)web.destroy();if(isFinishing()&&sessionUrl!=null&&Python.isStarted())new Thread(()->Python.getInstance().getModule("mobile_runtime").callAttr("stop",sessionUrl),"PerfectPower shutdown").start();super.onDestroy();}
}
