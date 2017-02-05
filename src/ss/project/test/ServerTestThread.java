package ss.project.test;

import ss.project.server.*;

public class ServerTestThread extends Thread {
    public Server server;
    
    public void run() {
        this.server = new Server();
        this.server.createView();
    }
    
    
}
