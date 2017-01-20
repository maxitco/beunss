package ss.week7.cmdline;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.Socket;

/**
 * Peer for a simple client-server application
 * @author  Theo Ruys
 * @version 2005.02.21
 */
public class Peer implements Runnable {
    public static final String EXIT = "exit";

    protected String name;
    protected Socket sock;
    protected BufferedReader in;
    protected BufferedWriter out;


    /*@
       requires (nameArg != null) && (sockArg != null);
     */
    /**
     * Constructor. creates a peer object based in the given parameters.
     * @param   nameArg name of the Peer-proces
     * @param   sockArg Socket of the Peer-proces
     */
    public Peer(String nameArg, Socket sockArg) throws IOException
    {
    	if(nameArg != null && sockArg != null) {
    		this.name = nameArg;
    		this.sock = sockArg;    	
    		this.in = new BufferedReader(new InputStreamReader(sock.getInputStream()));
    		this.out = new BufferedWriter(new OutputStreamWriter(sock.getOutputStream()));
    	} else {
    		throw new IOException("Input arguments should not be null");
    	}    	
    }

    /**
     * Reads strings of the stream of the socket-connection and
     * writes the characters to the default output.
     */
    public void run() {
    	try {
    		String line = null;
    		while((line = in.readLine()) != null) {	
    			System.out.println(name + ": " + line);     			
    		}
    	} catch (IOException e1) {
    		e1.getStackTrace();
    		return;
    	}
    	
    }


    /**
     * Reads a string from the console and sends this string over
     * the socket-connection to the Peer process.
     * On Peer.EXIT the method ends
     */
    public void handleTerminalInput() {
    	try {
    		System.out.println(this.getName() + " type message:");
    		BufferedReader standardInput = new BufferedReader(new InputStreamReader(System.in));
    		String input = standardInput.readLine();
    		while(input != null) {
    			if(input.equals(EXIT)) {
    				shutDown();
    				return;
    			} else {    			
    			out.write(this.getName() + ":	" + input);
    			out.newLine();
    			out.flush();
    			}
    		}
    	} catch (IOException e1) {
    		e1.getStackTrace();
    	}    	
    }

    /**
     * Closes the connection, the sockets will be terminated
     */
    public void shutDown() {
    	try { 
    		in.close();
    		out.close();
    		sock.close();    	
    	} catch (IOException e1) {
    		e1.getStackTrace();    		
    	}    
    }

    /**  returns name of the peer object*/
    public String getName() {
        return name;
    }
    
}
