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
	
	public void checkInput(String input) {
	    String[] inputSplit = input.split(" ");
	    
	    if (inputSplit[0].equals(Protocol.Client.SENDCAPABILITIES)) {
	        send(Protocol.Server.ASSIGNID + " " + getPlayerId());
	        this.game = new Game();
	    } else if ()
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
 