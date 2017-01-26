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
	private int id;
	private Game game;
	private String capabilities;
    
	
	public ClientHandler(Server inServer, Socket inSock) throws IOException {
    	this.server = inServer;
    	this.sock = inSock;      	
    	this.in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
		this.out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
		this.id = server.getHighestPlayerId() + 1;
    } 
	
	public void setPlayerName(String input) {
		this.playerName = input;
	}
	
	public String getPlayerName() {
	    return this.playerName;
	}	
	
	
	public int getPlayerId() {
	    return this.id;
	}
	
	
	public static int getPort(String input, String usage) {
    	int result = 0;
    	try {
    		result = Integer.parseInt(input);
        } catch (NumberFormatException e) {
            System.out.println(usage);
            System.out.println("ERROR: " + input
            		           + " is not an integer");
            System.exit(0);
        }
    	return result;
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
	
	//function to take action upon recieving input from the client
	public void checkInput(String input) {
	    //split input around spaces
	    String[] inputSplit = input.split(" ");
	    
	    //check which command is given (always the first word)
	    if (inputSplit[0].equals(Protocol.Client.SENDCAPABILITIES)) {
	        //store the input capabilities after removing the tag SENDCAPABILITIES
	        //also sets playername since it is sent with the capabilities
	        String storedCapabilities = "";
            for (int i = 1; i < 10; i++) {
                storedCapabilities.concat(" ".concat(inputSplit[i]));
            }
            this.capabilities = storedCapabilities;
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
            
            
	    } 
	}
    
    public void run() {
		String line = null; 
		try { 
		    //first action from the server, send capabilities as described in protocol
		    send(Protocol.Server.SERVERCAPABILITIES + Server.CAPABILITIES);		    
		    		    
			while (true) { 
				while ((line = in.readLine()) != null) {
				    checkInput(line);
				}
			} 
	  	} catch (IOException e) { 
	  		System.out.println("Something went wrong reading from socket"); 
	  	} 
    }
}
 