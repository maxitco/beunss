
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
        Socket sock = null;

        // parse args[1] - the port
        port = Peer.getPort(args[1], USAGE);
	  
    	// create ServerSocket    	   
        Server aServer = null;
    	try {
    		mainServerSocket = new ServerSocket(port);
    		aServer = new Server(mainServerSocket);
    		sock = aServer.getServerSocket().accept();
    	} catch (IOException e1) {
    		
    		System.out.println("ERROR: could not create a serversocket on port" + port);
    		
    		System.exit(0);
    	}
    	
    		
    	Peer.createPeer(name, sock);   	
    }

} // end of class Server
