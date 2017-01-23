
package ss.week7.cmdline;

import java.io.IOException;
import java.net.InetAddress;
import java.net.ServerSocket;
import java.net.Socket;
import java.net.UnknownHostException;

/**
 * Server. 
 * @author  Theo Ruys
 * @version 2005.02.21
 */
public class Server {
	private ServerSocket serverSocket;	
	
    private static final String USAGE
        = "usage: " + Server.class.getName() + " <name> <port>";

    public Server(ServerSocket inputServerSocket) {
    	if(inputServerSocket != null) {
    		this.serverSocket = inputServerSocket;
    	} else {
    		System.out.println("null input");
    	}
    }    
    
    public ServerSocket getServerSocket() {
    	return this.serverSocket;
    }
    /** Starts a Server-application. */
    public static void main(String[] args) {
    	// check input
    	if (args.length != 2) {
            System.out.println(USAGE);
            System.exit(0);
        }

        String name = args[0];
        InetAddress addr = null;
        int port = 0;
        ServerSocket mainServerSocket = null;

        // parse args[1] - the port
        try {
            port = Integer.parseInt(args[1]);
        } catch (NumberFormatException e) {
            System.out.println(USAGE);
            System.out.println("ERROR: port " + args[1]
            		           + " is not an integer");
            System.exit(0);
        }	
	  
    	// create ServerSocket    	   
        Server aServer = null;
    	try {
    		mainServerSocket = new ServerSocket(port);
    		aServer = new Server(mainServerSocket);
    	} catch (IOException e1) {
    		System.out.println("ERROR: could not create a socket on port" + port);
    		System.exit(0);
    	}
    	
    	
    	
    	
    	try {
    		
    		Socket sock = aServer.getServerSocket().accept();
    		
    		// create Peer object and start the two-way communication
            
            Peer server = new Peer(name, sock);
            Thread streamInputHandlerServer = new Thread(server);
            streamInputHandlerServer.start();
            server.handleTerminalInput();
            server.shutDown();
            
        	
    	} catch(IOException e1) {
    		e1.getStackTrace();
    	}    	
    }

} // end of class Server