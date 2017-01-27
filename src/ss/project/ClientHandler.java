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

public class ClientHandler extends Thread {
	private final Server server;
	private final Socket sock;
	private BufferedReader in;
	private BufferedWriter out;
	private String playerName;
	private int playerId;
	private Game game;
	private String clientCapabilities;
    
	
	public ClientHandler(Server inServer, Socket inSock) throws IOException {
    	this.server = inServer;
    	this.sock = inSock;      	
    	this.in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
		this.out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
		this.playerId = server.getHighestPlayerId() + 1;
    } 
	
	public void setPlayerName(String input) {
		this.playerName = input;
	}
	
	public String getPlayerName() {
	    return this.playerName;
	}	
	
	
	public int getPlayerId() {
	    return this.playerId;
	}
	
	public void setPlayerGame(Game inputGame) {
	    this.game = inputGame;
	}
	
	public void send(String input) {
	    try {
    	    out.write(input);
            out.newLine();
            out.flush();
	    } catch (IOException e) { 
            System.out.println("Something went wrong with sending through socket"); 
        } 
	}
	
	public void commandSendCapabilities (String[] inputSplit) {
	    //store the input capabilities after removing the tag SENDCAPABILITIES
        //also sets playername since it is sent with the capabilities
        String storedCapabilities = "";
        for (int i = 1; i < 10; i++) {
            storedCapabilities.concat(" ".concat(inputSplit[i]));
        }
        this.clientCapabilities = storedCapabilities;
        this.playerName = inputSplit[2];
        
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
            + this.game.getPlayerList().get(1).getPlayerId()
            + "|" + this.game.getPlayerList().get(1).getPlayerName()
            + "0000ff"
            + " "
            + this.game.getPlayerList().get(2).getPlayerId()
            + "|" + this.game.getPlayerList().get(2).getPlayerName()
            + "ff0000"  
            );
        
        //start game loop
        this.game.startGame();    
	}
	
	//function to take action upon receiving input from the client
	public void handleInput(String input) {
	    //split input around spaces
	    String[] inputSplit = input.split(" ");
	    
	    //check which command is given (always the first word)
	    if (inputSplit[0].equals(Protocol.Client.SENDCAPABILITIES)) {
	        commandSendCapabilities(inputSplit);
	    } else if (inputSplit[0].equals(Protocol.Client.MAKEMOVE)) {
	        
	    } else {
	        send("error 4"); //error 4 ==> invalidCommand
	    }
	    
	}
    
    public void run() {
		String line = null; 
		try { 
		    //first action from the server, send capabilities as described in protocol
		    send(Protocol.Server.SERVERCAPABILITIES + Server.CAPABILITIES);		    
		    		    
			while (true) { 
				while ((line = in.readLine()) != null) {
				    handleInput(line);
				}
			} 
	  	} catch (IOException e) { 
	  		System.out.println("Something went wrong reading from socket"); 
	  	} 
    }
}
 