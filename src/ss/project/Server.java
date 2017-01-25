package ss.project;

import java.io.IOException;
import java.net.InetAddress;
import java.net.ServerSocket;
import java.net.Socket;

public class Server {
private ServerSocket serverSocket;	
	
    private static final String USAGE
        = "usage: " + Server.class.getName() + " <name> <port>";

    //constructor for server, create ServerSocket
    public Server(int port) throws IOException, PortException {
    	if (port > 0) {
			this.serverSocket = new ServerSocket(port);			
    	} else {
    		throw new PortException();
    	}
    }    
    
    public ServerSocket getServerSocket() {
    	return this.serverSocket;
    }
    
    
    /** Starts a Server-application. */
    /*
     * args[0] --> port
     */
    public static void main(String[] args) {
    	// check input
    	if (args.length != 1) {
            System.out.println(USAGE);
            System.exit(0);
        }      
        
        // parse args[0] - the port
        int port = ClientHandler.getPort(args[0], USAGE);
	  
    	// create a Server        
    	try {
    		Server aServer = new Server(port);
    		Socket sock = aServer.getServerSocket().accept();
    	} catch (IOException e1) {    		
    		System.out.println("ERROR: could not create a serversocket on port" + port);    		
    		System.exit(0);
    	} catch (PortException e2) {
    		System.out.println("port should be larger than 0, but was:" + port);    		
    		System.exit(0);
    	}   	
    }

} // end of class Server

