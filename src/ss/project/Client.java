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
    private boolean online;
    private boolean inGame = false;
    
    
    public Client() throws IOException {
        super(System.in, System.out);
        this.playerName = "NoNamePepe";     //should be overwritten           
    }
    
    public void setPlayerName(String input) {
        this.playerName = input;
        
    }
    
    /*@ pure */ public String getPlayerName() {
        return this.playerName;
    }   
    
    /*@ pure */ public boolean isOnline() {
        return this.online;
    }
    
    /*@ pure */ public boolean isInGame() {
        return this.inGame;
    }
    
    /*@ pure */ public String getCapabilities() {
        return Protocol.Client.SENDCAPABILITIES + " 2 " + this.playerName + "4 4 4 4 0 0";
    }
    
    @Override
    public void atStart() {
        send("Enter 'online <server IP adress> <Socket>' to start an online game or 'offline' to play against AI ");        
    }
    
    @Override
    public void handleInput(String input) {
      //split input around spaces
        String[] inputSplit = input.split(" ");
        
        if (inputSplit[0].equals("online")) {
            connectToServer(inputSplit[1], inputSplit[2]);
            send("connecting to server...");     
            this.online = true;
        } else if (inputSplit[0].equals("offline")) {
            connectToServer("localhost", "2728");
            send("setting up game...");
            this.online = false;
        } else if (inputSplit[0].equals("EXIT")) {
            System.exit(0);
        }        
    }
    
    public void connectToServer(String ip, String socket) {
        InetAddress addr = null;
        Socket sock = null;
        int port = Server.getPort(socket);
        
        // check args[1] - the IP-adress
        try {
            addr = InetAddress.getByName(ip);
        } catch (UnknownHostException e) {
            send(USAGE);
            send("ERROR: host " + ip + " unknown.");
            atStart();
        }
        
        // try to open a Socket 
        try {
            sock = new Socket(addr, port);
            this.serverHandler = new ServerHandler(this, sock);
            this.serverHandler.start();
        } catch (IOException e) {
            send("ERROR: could not create a socket on " + addr
                    + " and port " + port);
            atStart();
        }        
    }
    
    /** Starts a Client application. */
    public static void main(String[] args) {
        //construct a client
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
