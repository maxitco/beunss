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
	private int ID;
    
	
	public ClientHandler(Server inServer, Socket inSock) throws IOException {
    	this.server = inServer;
    	this.sock = inSock;      	
    	this.in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
		this.out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
    } 
	
	public void setPlayerName(String input) {
		this.playerName = input;
	}
	
	
	public static int getPort(String input, String USAGE) {
    	int result = 0;
    	try {
    		result = Integer.parseInt(input);
        } catch (NumberFormatException e) {
            System.out.println(USAGE);
            System.out.println("ERROR: " + input
            		           + " is not an integer");
            System.exit(0);
        }
    	return result;
    }
    
    public void run() {
    	  String line = null; 
    	  try { 
    		  while (true) { 
    			  while ((line = in.readLine()) != null) {
    				  
    			  }
    		  } 
    	  } catch (IOException e) { 
    		  System.out.println("Something went wrong reading from socket"); 
    	  } 
    }
}
 