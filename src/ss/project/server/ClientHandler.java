package ss.project.server;

import java.io.IOException;
import java.net.Socket;

import ss.project.game.Game;
import ss.project.game.Protocol;
import ss.project.view.Terminal;


public class ClientHandler extends Terminal implements Runnable {
	private final Server server;
	private String playerName = "notSendYet";
	private int playerId;
	private Game game;
	private boolean canChat;
	public boolean disconnected = false;
	
	/*
	 * variable below is not necessary since we run the basic game
	 * private String[] clientCapabilities;
	 */
    
	public ClientHandler(Server inServer, Socket inSock) throws IOException {
    	super(inSock.getInputStream(), inSock.getOutputStream());
    	this.server = inServer;    			
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
        if (inputSplit.length > 8 && inputSplit[8].equals("1")) {
            this.canChat = true; 
        } else {
            this.canChat = false;
        }
	}
	
	@Override
	public void send(String input) {
	    if (!disconnected) {
	        super.send(input);
	    }
	    //send all communication (except pings) to serverTUI as required
	    if (!input.equals("ping")) {
	        this.server.sendToView("sent(To " + this.playerName + "): " + input);
	    }
	}
	
	@Override
	public void atStart() {
	    //first action from the server, send capabilities as described in protocol
	    send(Protocol.ProtServer.SERVERCAPABILITIES + Server.CAPABILITIES); 
	}
	
	@Override
	public void onFailure() {
	    this.disconnected = true;
	    if (this.game != null) {
	        this.game.leaveGame(this);
	    }
	    
	    if (this.server != null) {
	        this.server.leaveServer(this);
	    }
	    
	    //exit the terminal and close its streams.
	    super.exit();	    
	}
	//function to determine which action should be performed upon receiving input from the client
	@Override
	public void handleInput(String input) {
	    //send communication to serverTUI as required
	    this.server.sendToView("client (" + this.playerName + "): " + input);
	    //split input around spaces
	    String[] inputSplit = input.split(" ");
	    
	    //check which command is given (always the first word)
	    if (inputSplit[0].equals(Protocol.ProtClient.SENDCAPABILITIES)) {
	        setClientCapabilities(inputSplit);
	        this.server.joinGame(this);
	    } else if (inputSplit[0].equals(Protocol.ProtClient.SENDMESSAGE) && this.canChat) {
	        this.server.sendChat(inputSplit, this.playerName);
	    } else if (inputSplit[0].equals(Protocol.ProtClient.MAKEMOVE) && inputSplit.length == 3) {
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
 