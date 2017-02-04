package ss.project.server;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;


import ss.project.game.Game;
import ss.project.view.View;
import ss.project.view.ServerTUIView;

public class Server extends Thread {
	private ServerSocket serverSocket;	
	private View view;
	public boolean running = false; 
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
    //@ensures this.getServerSocket().isBound();
    public Server() {    		
		try {
		    this.view = new ServerTUIView(this);
		    this.view.run();
		} catch (IOException e1) {
		    System.out.println("Could not create TUI vor server.");
		    System.exit(0);
		}
    }
    
    public void setPort(int port) throws IOException {       
        this.serverSocket = new ServerSocket(port);
    }
    
    
    
    public void startServer(String input) {
        if (this.running) {
            sendToView("Server already running, exit and restart to run server on different port.");
        } else {
            this.running = true;
            // parse input - the port
            int port = getPort(input);
            try {
                setPort(port);
                this.start();
            } catch (IOException e1) {
                sendToView("Could not create ServerSocket on port: " + port);   
                sendToView("Try again.");
                this.running = false;
            }
        }
    }
    
    public void run() {
        accepter(); 
    }
    
    public void sendToView(String input) {
        this.view.send(input);
    }    
    
    /**Notifies all clients that shutdown will happen, then exit the program and all its threads.
     * 
     */
    
    public void shutDown() {
        for (ClientHandler client: this.clientHandlerList) {
            client.send("serverdown");
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
    public void accepter() {
        
        sendToView("Server started, ready to accept incoming connections");
        while (true) {
    	    Socket sock = null;
    	    try {
    	        sock = this.getServerSocket().accept();
    	        sendToView("New client connected!");
    	    } catch (IOException e1) {
    	        sendToView("Could not accept connection on serversocket.");
    	    }
    	    
    	    try {
    	        ClientHandler clientHandler = new ClientHandler(this, sock);
    	        this.clientHandlerList.add(clientHandler);
    	        clientHandler.start();
    	    } catch (IOException e1) {
                sendToView("Could not create client handler.");
            }
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
    	//create a new server
    	new Server();          	
    }

} // end of class Server

