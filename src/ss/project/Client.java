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
    private Board board;
    private ServerHandler serverHandler;
    private boolean online;
    private boolean inGame = false;
    private int currentTurnId;
    
    
    public Client() throws IOException {
        super(System.in, System.out);
        this.playerName = "NoNamePepe";     //should be overwritten           
    }
    public void refreshBoard() {
        this.board = new Board();
    }
    
    public void setPlayerName(String input) {
        this.playerName = input;        
    }
    
    public void setPlayerId(int input) {
        this.playerId = input;
    }
    
    public void setCurrentTurnId(int input) {
        this.currentTurnId = input;
    }
    
    public void setInGame(boolean input) {
        this.inGame = input;
    }
    
    /*@ pure */ public String getPlayerName() {
        return this.playerName;
    }  
    
    /*@ pure */ public int getPlayerId() {
        return this.playerId;
    }  
    
    /*@ pure */ public Board getBoard() {
        return this.board;
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
        send("Enter 'online <server IP adress> <Socket> <Your player name>' to start an online game or 'offline' to play against AI ");        
    }
    
    @Override
    public void handleInput(String input) {
        if (input != null) {
            
            //split input around spaces
            String[] inputSplit = input.split(" ");
            
            if (inputSplit[0].equals("online") && inputSplit.length == 4) {
                setPlayerName(inputSplit[3]);
                connectToServer(inputSplit[1], inputSplit[2]);
                send("connecting to server...");     
                this.online = true;
            } else if (inputSplit[0].equals("offline")) {
                connectToServer("localhost", "2728");
                send("setting up game...");
                this.online = false;
            } else if (inputSplit[0].equals("EXIT")) {
                System.exit(0);
            } else if (inputSplit[0].equals("MOVE") && inputSplit.length == 3 && this.inGame) {
                serverHandler.send(Protocol.Client.MAKEMOVE + " " + inputSplit[1] + " " + inputSplit[2]);
            } else {
                send(
                    "You entered: '" + input 
                    + "' which is not valid input or can only be done if it is your turn in the game."
                );
                
                if (this.inGame) {
                    if (this.currentTurnId != this.playerId) {
                        send("Note that it is not your turn now");
                    }
                } else {
                    send("Note that you are not in game right now");
                }          
            }
        } else {
            send("null input, y u do this?");
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
