package ss.project;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;

public class ClientHandler extends Terminal {
	private final Server server;
	private final Socket sock;
	private String playerName;
	private int playerId;
	private Game game;
	/*
	 * variable below is not necessary since we run the basic game
	 * private String[] clientCapabilities;
	 */
    
	public ClientHandler(Server inServer, Socket inSock) throws IOException {
    	super(inSock.getInputStream(), inSock.getOutputStream());
	    this.server = inServer;
    	this.sock = inSock;      	
		inServer.obtainPlayerId(this);
    } 
	

	
	//@requires input != null;
	//@ensures getPlayerName().equals(input);
	public void setPlayerName(String input) {
		this.playerName = input;
	}
	
	//@ensures getPlayerId() == id;
    public void setPlayerId(int id) {
        this.playerId = id;
    }
    
    //@requires inputGame != null;
    //@ensures getPlayerGame() == inputGame;
    public void setPlayerGame(Game inputGame) {
        this.game = inputGame;
    }
	
    
	/*@ pure*/ public String getPlayerName() {
	    return this.playerName;
	}	
	
	
	/*@ pure */ public int getPlayerId() {
	    return this.playerId;
	}
	
    /*@ pure */ public Game getPlayerGame() {
        return this.game;
    }	
	
	/* 
     * sets playerName since it is sent with the capabilities
     * could be used to store clientCapabilites
     * but this is not done since we only have the basic game
     * so the client should be able to handle all the commands we send to it
     */
	
	//@requires inputSplit.length == 10;
	//@ensures getPlayerName().equals(inputSplit[2]);    
	public void setClientCapabilities(String[] inputSplit) {
        // this.clientCapabilities = inputSplit;
        this.playerName = inputSplit[2];
	}
    
	public void setupGameForClient() {
        //send the playerID to the player
        //ID was already known since it is set in the constructor
        //however the protocol mandates this is the time to send it
        send(Protocol.Server.ASSIGNID + " " + getPlayerId());
        
        //make a new game or join a current one
        server.joinGame(this);  
        
        //wait till game is full
        while (!this.game.isFull()) {
            
        }
        
        //notify player that the game has started   
        //includes game specifications and opponent info
        send(
            Protocol.Server.STARTGAME 
            + " 4|4|4|4 " 
            + this.game.getPlayerList().get(0).getPlayerId()
            + "|" + this.game.getPlayerList().get(0).getPlayerName()
            + "0000ff"
            + " "
            + this.game.getPlayerList().get(1).getPlayerId()
            + "|" + this.game.getPlayerList().get(1).getPlayerName()
            + "ff0000"  
        );
        
        //start game loop
        this.game.startGame();    
	}
	
	@Override
	public void atStart() {
	    //first action from the server, send capabilities as described in protocol
	    send(Protocol.Server.SERVERCAPABILITIES + Server.CAPABILITIES); 
	}
	
	//function to determine which action should be performed upon receiving input from the client
	@Override
	public void handleInput(String input) {
	    //split input around spaces
	    String[] inputSplit = input.split(" ");
	    
	    //check which command is given (always the first word)
	    if (inputSplit[0].equals(Protocol.Client.SENDCAPABILITIES)) {
	        setClientCapabilities(inputSplit);
	        setupGameForClient();
	    } else if (inputSplit[0].equals(Protocol.Client.MAKEMOVE) && inputSplit.length == 3) {
	        try {
	            int x = Integer.parseInt(inputSplit[1]);
	            int y = Integer.parseInt(inputSplit[2]);
	            this.game.makeMove(x, y, this);
	        } catch (NumberFormatException e) {
	            send("error 4"); //error 4 ==> invalidCommand
	        }
	        
	    } else {
	        send("error 4"); //error 4 ==> invalidCommand
	    }
	    
	}
}
 