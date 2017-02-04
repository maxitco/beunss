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
    //@requires port > 0;
    //@ensures this.getServerSocket() != null;
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
    
    /** Returns gameList.
     * 
     */
    /*@ pure */ public ArrayList<Game> getGameList() {
    	return this.gameList;
    }
    /** Creates ClientHandler for new connection.
     * 
     * @throws IOException
     */
    //@ensures this.getClientHandlerList().size() == \old(this.getClientHandlerList().size()) + 1;
    public void accepter() throws IOException {
    	while (true) {
    		Socket sock = this.getServerSocket().accept();
    		System.out.println("New client connected!");
    		ClientHandler clientHandler = new ClientHandler(this, sock);
    		this.clientHandlerList.add(clientHandler);
    		clientHandler.start();
    	}
    }
    /**join an available game or if none is available create a new game for the player.
     * synchronized to prevent 2 players joining an existing game at the same moment.
     * 
     * @param inputPlayer
     */
    //@requires inputPlayer != null;
    //@ensures this.getClientHandlerList().size() - (this.getGameList().size() * 2) < 2;
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
    /** Retrieves port number from string.
     * 
     * @param input
     * @return
     */
    //@requires input != null && input.length() > 0;
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
    
    /** Starts a Server-application.
     *
     * @param args[0] --> port
     */
    //@requires getPort(args[0]) != 0;
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

