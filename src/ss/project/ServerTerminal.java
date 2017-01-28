package ss.project;

import java.io.IOException;

public class ServerTerminal extends Terminal {
    private final Server server;
    private final static String EXIT = "EXIT"; 
    private final static String HELP = "HELP"; 
    
    public ServerTerminal(Server inServer) throws IOException {
        super(System.in, System.out);
        this.server = inServer;      
    } 
    
    @Override
    public void atStart() {
        send("server started\n");
        send("Enter a command below.");
    }
    
    @Override
    public void handleInput(String input) {
        if (input.equals(EXIT)) {
            super.send("Server is shutting down...");
            server.shutDown();
        } else if (input.equals(HELP)) {
            super.send("");
            super.send("VALID COMMANDS");
            super.send("Command:'" + EXIT + "' ==> shutdown the server.");
            super.send("");
            super.send("Enter a command below.");
        } else {
            super.send("Invalid command, type 'HELP' to see valid commands.");
        }
        
    }    
}
