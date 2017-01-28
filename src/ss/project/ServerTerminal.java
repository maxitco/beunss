package ss.project;

import java.io.IOException;

public class ServerTerminal extends Terminal implements Runnable {
    private final Server server;
    private final static String EXIT = "EXIT"; 
    private final static String HELP = "HELP"; 
    
    public ServerTerminal(Server inServer) throws IOException {
        super();
        this.server = inServer;      
    } 
    
    /* @Override */
    public void handle(String input) {
        if (input.equals(EXIT)) {
            server.shutDown();
        } else if (input.equals(HELP)) {
            System.out.println("valid commands:");
            System.out.println(EXIT + ": shutdown the server.");
        } else {
            System.out.println("Invalid command, type HELP to see valid commands.");
        }
        System.out.println("type here: ");
    }
    
    public void run() {
        write();
    }
}
