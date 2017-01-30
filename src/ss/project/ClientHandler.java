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
    	System.out.println("here we are");
    	this.server = inServer;
    	this.sock = inSock;      	
    	System.out.println("here we are2");		
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
	        server.joinGame(this);
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
 