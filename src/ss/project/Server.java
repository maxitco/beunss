package ss.project;

import java.io.IOException;
import java.net.InetAddress;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;

public class Server {
private ServerSocket serverSocket;	
	private static final String name = "ServerJR"; 
    private static final String USAGE
        = "usage: " + Server.class.getName() + " <name> <port>";
    private ArrayList<ClientHandler> clientHandlerList = new ArrayList<ClientHandler>();

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
    
    public static String getName() {
    	return name;
    }
    
    public void accepter() throws IOException {
    	while (true) {
    		Socket sock = this.getServerSocket().accept();
    		System.out.println("New client connected!");
    		ClientHandler clientHandler = new ClientHandler(this, sock);
    		clientHandlerList.add(clientHandler);
    		clientHandler.start();    		
    	}
    }
    
    
    /** Starts a Server-application. */
    /*
     * args[0] --> port
     */
    public static void main(String[] args) {
    	// check input
    	if (args.length != 1) {
            System.out.println(USAGE);
            System.out.println("Input is not of length 1");
            System.exit(0);
        }      
        
        // parse args[0] - the port
        int port = ClientHandler.getPort(args[0], USAGE);
	  
    	// create a Server       
    	try {
    		new Server(port).accepter();;
    		
    	} catch (IOException e1) {    		
    		System.out.println("ERROR: could not create a serversocket on port" + port);    		
    		System.exit(0);
    	} catch (PortException e2) {
    		System.out.println("port should be larger than 0, but was:" + port);    		
    		System.exit(0);
    	}   	
    }

} // end of class Server

