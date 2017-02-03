package ss.project.server;

import java.io.IOException;
import java.net.InetAddress;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;

import ss.project.game.Game;
import ss.project.view.ServerTerminal;

public class Server {
	private ServerSocket serverSocket;	
	private ServerTerminal serverTerminal;
	public static final String NAME = "ServerJR"; 
	public static final String CAPABILITIES = " 2 0 4 4 4 4 0";
  
    
    private ArrayList<ClientHandler> clientHandlerList = new ArrayList<ClientHandler>();
    private ArrayList<Game> gameList = new ArrayList<Game>();
    
    /**constructor for server, creates ServerSocket.
     * 
     * @param port 
     * @throws IOException
     * @throws PortException
     */
    public Server(int port) throws IOException, PortException {
    	if (port > 0) {
			this.serverSocket = new ServerSocket(port);	
			this.serverTerminal = new ServerTerminal(this);
			serverTerminal.start();
    	} else {
    		throw new PortException();
    	}
    }
    
    /**Notifies all clients that shutdown will happen, then exit the program and all its threads.
     * 
     */
    public void shutDown() {
        for (ClientHandler client: this.clientHandlerList) {
            client.send("error 1"); //TODO fix better error
        }
        System.exit(0);
    }
    
    /**Returns the server socket.
     * 
     * @return
     */
    /*@ pure */ public ServerSocket getServerSocket() {
    	return this.serverSocket;
    }
    
    /** Returns the List of Clienthandlers.
     * 
     * @return ArrayList<ClientHandler>
     */
    /*@ pure */ public ArrayList<ClientHandler> getClientHandlerList() {
        return this.clientHandlerList;
    }
    
    /** 
     * 
     * @throws IOException
     */
    public void accepter() throws IOException {
    	while (true) {
    		Socket sock = this.getServerSocket().accept();
    		System.out.println("New client connected!");
    		ClientHandler clientHandler = new ClientHandler(this, sock);
    		this.clientHandlerList.add(clientHandler);
    		clientHandler.start();
    	}
    }
    /**
     * 
     * @param inputPlayer
     */
    //synchronized to prevent 2 players joining an existing game at the same moment.
    //join an available game or if none is available create a new game for the player.
    public synchronized void joinGame(ClientHandler inputPlayer) {
        //search for available games and start them && and player if found
        Game game = null;
        int i = 0;
        //search for game available to join
        while (game == null && i < this.gameList.size()) {
            //game is available if it is not full
            if (!this.gameList.get(i).isFull()) {
                System.out.println("game " + i + " was joined");
                game = this.gameList.get(i);                
            }
            i++; //continue
        }
        
        //if no game found make a new one
        if (game == null) {
            System.out.println("new game created");
            game = new Game(); 
            this.gameList.add(game);
        }
        //add the handler to the game        
        game.addPlayer(inputPlayer);
        //add the game to the handler 
        inputPlayer.setPlayerGame(game);
        
        //start the game if it is full
        if (game.isFull()) {
            game.start();
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
            System.out.println("ERROR: " + input
                               + " is not an integer");
            
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

