package ss.project.server;

public class PingThread extends Thread {
    private Server server;
    
    public PingThread(Server inServer) {
        this.server = inServer;
    }
    
    public void run() {
        //this.server.pingAll();
    }
}
