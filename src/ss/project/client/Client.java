package ss.project.client;

import java.io.IOException;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;
import ss.project.game.Protocol;
import ss.project.game.Board;
import ss.project.game.Field;
import ss.project.game.Mark;
import ss.project.server.Server;
import ss.project.view.ClientView;
import ss.project.view.ClientTUIView;
 
public class Client {    
    private String playerName;
    public String opponentName;
    private int playerId;
    private Board board;
    private ServerHandler serverHandler;
    private boolean online;
    private boolean inGame = false;
    private int currentTurnId;
    private ClientView view;  
    private boolean aiEnabled = false;
    public boolean canChat;
    private ComputerPlayer ai = new ComputerPlayer(new Hard());
    
    //set standard name for AI
    //view creation is not done in constructor, as for AI clients it is not desired
    public Client() {
        this.playerName = "NoNamePepeAI";     
    }
    
    //creates a view for the client
    public void createNewView() {
        try {
            this.view = new ClientTUIView(this);
            this.view.run();
        } catch (IOException e1) {
            System.out.println("could not create view");
            System.exit(0);
        }       
    }
    
    public boolean toggleAI() {
        this.aiEnabled = !this.aiEnabled;
        return aiEnabled;
    }
    
    public String hint() {
        if (inGame && this.currentTurnId == this.playerId) {
            Field field = this.ai.determineMove(this.board, Mark.Black);
            return "move(x y): " + field.getMove();
        }  else {
            return "Hint is only available when it is your turn in game.";
        }
    }
    
    /*
     * ServerHandler functions
     */
    public void atAI(String[] inputSplit) {
        Client client = new Client();
        if (inputSplit[2].equals("easy")) {            
            client.setAI(new ComputerPlayer(new Easy()));
        } else if (inputSplit[2].equals("medium")) {
            client.setAI(new ComputerPlayer(new Medium()));
        } else if (inputSplit[2].equals("hard")) {
            client.setAI(new ComputerPlayer(new Hard()));
        }
        //turn the ai on
        client.toggleAI();
        client.connectToServer("localhost", inputSplit[1]);
    }
    
    public void atTurnOfPlayer(String[] inputSplit) {
        //notify the player whose turn it is
        try {
            //get the id of the current player
            int id = Integer.parseInt(inputSplit[1]);
            setCurrentTurnId(id);

            //compare current player to clientId to see who it is
            if (id == getPlayerId()) {
                sendToView("It is your turn, type: 'move <x> <y>' to make a move.");
                //let the AI make a move for you
                if (this.aiEnabled) {
                    Field field = this.ai.determineMove(board, Mark.Black);
                    sendToServer(Protocol.ProtClient.MAKEMOVE + " " + field.getMove());
                }
            } else {
                sendToView("It is the turn of player " + this.opponentName);
            }                
        } catch (NumberFormatException e) {
            sendToView("Server is sending rubbish, NumberFormatException");
        }
    }
    
    public void setOnline(boolean input) {
        this.online = input;
    }
    
    /*@ pure */ public ServerHandler getServerHandler() {
        return this.serverHandler;
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
    
    public void setAI(ComputerPlayer player) {
        this.ai = player;
    }
    
    public int getCurrentTurnId() {
        return this.currentTurnId;
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
        return Protocol.ProtClient.SENDCAPABILITIES + " 2 " + this.playerName + " 0 4 4 4 4 1 0";
    }
    
    public void sendToServer(String input) {
        if (this.serverHandler != null) {
            this.serverHandler.send(input);
        } else {
            sendToView("Error connection to server is required for this action.");
        }
    }
    
    public void sendToView(String input) {
        if (this.view != null) {
            this.view.send(input);
        }
    }
    
    public void connectToServer(String ip, String socketPort) {
        InetAddress addr = null;
        
        int port = Server.getPort(socketPort);
        
        // check args[1] - the IP-adress
        try {
            addr = InetAddress.getByName(ip);
        } catch (UnknownHostException e) {
            sendToView("ERROR: host " + ip + " unknown."); 
            sendToView("try again");
        }
        
        // try to open a Socket 
        try {
            Socket sock = new Socket(addr, port);
            this.serverHandler = new ServerHandler(this, sock);
            new Thread(this.serverHandler).start();
            sendToView("setting up game...");
        } catch (IOException e) {
            sendToView("ERROR: could not create a socket on " + addr
                    + " and port " + port);            
            sendToView("try again");
        }        
    }
    
    //resets the client
    public void restart() {
        sendToView("\n\nRestarting...");
        if (this.serverHandler != null) {
            this.serverHandler.exit();
        }
        this.inGame = false;
        this.view.atStart();        
    }
    
    /** Starts a Client application. */
    public static void main(String[] args) {
        //construct a client
        Client aClient = new Client();
        aClient.createNewView();        
    }
}
