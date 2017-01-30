package ss.project;

import java.io.IOException;
import java.net.InetAddress;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;

public class Server {
	private ServerSocket serverSocket;	
	private ServerTerminal serverTerminal;
	public static final String NAME = "ServerJR"; 
	public static final String CAPABILITIES = ""; //TODO write string
    private static final String USAGE
        = "usage: " + Server.class.getName() + " <name> <port>";
    
    private ArrayList<ClientHandler> clientHandlerList = new ArrayList<ClientHandler>();
    private ArrayList<Game> gameList = new ArrayList<Game>();
    
    //constructor for server, create ServerSocket
    public Server(int port) throws IOException, PortException {
    	if (port > 0) {
			this.serverSocket = new ServerSocket(port);	
			this.serverTerminal = new ServerTerminal(this);
			serverTerminal.start();
    	} else {
    		throw new PortException();
    	}
    }    
    
    //shutdown, notify all clients that shutdown will happen
    //exit the program and all its threads
    public void shutDown() {
        for (ClientHandler client: this.clientHandlerList ) {
            client.send("error 1"); //TODO fix better error
        }
        System.exit(0);        
    }
    
    /*@ pure */ public ServerSocket getServerSocket() {
    	return this.serverSocket;
    }    

    /*@ pure */ public ArrayList<ClientHandler> getClientHandlerList() {
        return this.clientHandlerList;
    }
    
    public void accepter() throws IOException {
    	while (true) {
    		Socket sock = this.getServerSocket().accept();
    		System.out.println("New client connected!");
    		ClientHandler clientHandler = new ClientHandler(this, sock);
    		System.out.println("ClientHandler made");
    		this.clientHandlerList.add(clientHandler);
    		System.out.println("ClientHandler added to list");
    		clientHandler.start();
    		System.out.println("ClientHandler started");
    	}
    }
    
    /*
     * synchronized to prevent players from getting the same ID 
     * if their clients call function at same moment    
     */
    
    //@requires idLessClient != null;
    /*@ensures (\forall ClientHandler c; c != idLessClient && getClientHandlerList().contains(c);
     idLessClient.getPlayerId() > c.getPlayerId());
    */    
    public synchronized void obtainPlayerId(ClientHandler idLessClient) {
        int result = 0;
        System.out.println("didchagethere?");
        for (int i = 0; i < clientHandlerList.size(); i++) {            
            if (clientHandlerList.get(i).getPlayerId() > result) {
                result = clientHandlerList.get(i).getPlayerId();
            }
        }
        
        System.out.println("didchagethere2?");
        idLessClient.setPlayerId(result + 1);
        System.out.println("didchagethere?3");
    }
    
    //join an available game or if none is available create a new game for the player.
    public synchronized void joinGame(ClientHandler inputPlayer) {
        
        //search for available games && and player if found
        boolean found = false;
        int i = 0;
        while (!found && i < gameList.size()) {
            if (!this.gameList.get(i).isFull()) {
                this.gameList.get(i).addPlayer(inputPlayer);
                inputPlayer.setPlayerGame(this.gameList.get(i));
                found = true;
            }
        }
        
        //construct new game if no available game is found
        if (!found) {
            Game aNewGame = new Game();
            aNewGame.addPlayer(inputPlayer);
            inputPlayer.setPlayerGame(aNewGame);
            this.gameList.add(aNewGame);            
        }
    }    
    
    //getPort function to retrieve port from input
    //@requires input != null;
    //@ensures \result == Integer.parseInt(input) || \result == 0;
    /*@ pure */ public static int getPort(String input) {
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
        int port = getPort(args[0]);
	  
    	// create a Server       
    	try {
    	    
    		new Server(port).accepter();
    		
    	} catch (IOException e1) {    		
    		System.out.println("ERROR: could not create a serversocket on port" + port);    		
    		System.exit(0);
    	} catch (PortException e2) {
    		System.out.println("port should be larger than 0, but was:" + port);    		
    		System.exit(0);
    	}   	
    }

} // end of class Server

