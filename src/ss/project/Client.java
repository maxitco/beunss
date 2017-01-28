package ss.project;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;



public class Client extends Terminal {
    private static final String USAGE
        = "usage: java week7.cmdline.Client <name> <address> <port>";

    private Socket sock;
    private String playerName;
    private int playerId;
    private Game game;
    private ServerHandler serverHandler;
    
    
    public Client() throws IOException {
        super(System.in, System.out);
        this.playerName = "NoNamePepe";                
    }
    
    public void setPlayerName(String input) {
        this.playerName = input;
    }
    
    public String getCapabilities() {
        return ""; //TODO
    }
    
    @Override
    public void atStart() {
        send("Enter 'online' to start an online game or 'offline' to play against AI ");        
    }
    
    @Override
    public void handleInput(String input) {
        
    }
    
    /** Starts a Client application. */
    public static void main(String[] args) {
        //construct a wonderful client absolutely splendid
        Client aClient = null;
        try {
            aClient = new Client();
        } catch (IOException e1) {
            System.out.println("Desmond the moon bear");
        }
        //Start the client
        aClient.start();
    }
}
