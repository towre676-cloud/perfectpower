package com.perfectpower.explorer;
import android.app.Service;
import android.content.Intent;
import android.os.*;
import com.chaquo.python.Python;
import com.chaquo.python.android.AndroidPlatform;
import java.nio.file.*;
import java.nio.charset.StandardCharsets;

public class EngineService extends Service {
    private final Messenger messenger = new Messenger(new Handler(Looper.getMainLooper()) {
        @Override public void handleMessage(Message message) {
            if (message.what == 2) { android.os.Process.killProcess(android.os.Process.myPid()); return; }
            if (message.what != 1) return;
            final Messenger reply = message.replyTo;
            final String path = message.getData().getString("path");
            new Thread(() -> {
                String result;
                try {
                    if (!Python.isStarted()) Python.start(new AndroidPlatform(EngineService.this));
                    result = Python.getInstance().getModule("mobile_runtime").callAttr("execute",new String(Files.readAllBytes(Path.of(path)),StandardCharsets.UTF_8)).toString();
                } catch (Throwable error) {
                    result = "{\"exit_code\":1,\"error\":" + org.json.JSONObject.quote(error.toString()) + "}";
                }
                Message answer=Message.obtain(null,3);Bundle data=new Bundle();data.putString("result",result);answer.setData(data);
                try { reply.send(answer); } catch (RemoteException ignored) { }
            },"PerfectPower engine").start();
        }
    });
    @Override public IBinder onBind(Intent intent) { return messenger.getBinder(); }
}
