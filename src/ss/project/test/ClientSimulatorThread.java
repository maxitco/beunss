package ss.project.test;
import ss.project.client.*;

public class ClientSimulatorThread extends Thread {
    private Client client;
    public void run() {
        this.client.setOnline(true);
        this.client.setPlayerName("simulator");
        this.client.connectToServer("localhost", "10");
    }
}
