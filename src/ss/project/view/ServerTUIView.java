package ss.project.view;

import java.io.IOException;
import ss.project.server.Server;

public class ServerTUIView extends Terminal implements View {
    private final Server server;
    private final static String START = "start";
    private final static String EXIT = "exit"; 
    private final static String HELP = "help";
    private final static String SWITCH = "switch";
    
    public ServerTUIView(Server inServer) throws IOException {
        super(System.in, System.out);
        this.server = inServer;      
    } 
    
    @Override
    public void atStart() {
        send("Enter 'start <port>' to start the server.");
    }
    
    @Override
    public void handleInput(String input) {
        String[] inputSplit = input.split(" ");
        if (input.equals(EXIT)) {
            super.send("Server is shutting down...");
            server.shutDown();
        } else if (inputSplit[0].equals(START) && inputSplit.length == 2) {
            this.server.startServer(inputSplit[1]);            
        } else if (input.equals(HELP)) {
            super.send("");
            super.send("VALID COMMANDS");
            super.send("Command:'" + START + "' ==> starts the server on port.");
            super.send("Command:'" + EXIT + "' ==> shutdown the server.");
            super.send("");
            super.send("Enter a command below.");
        } else if (input.equals(SWITCH)) {
            super.send("");
        } else {
            super.send("Invalid command, type 'HELP' to see valid commands.");
        }
        
    }       
}
