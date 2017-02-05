package ss.project.server;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;


import ss.project.game.Game;
import ss.project.game.Protocol;
import ss.project.view.View;
import ss.project.view.ServerTUIView;

public class Server extends Thread {
	private ServerSocket serverSocket;	
	private View view;
	public boolean running = false; 
	public static final String CAPABILITIES = " 2 0 4 4 4 4 1";
	
    private ArrayList<ClientHandler> clientHandlerList = new ArrayList<ClientHandler>();
    private ArrayList<Game> gameList = new ArrayList<Game>();
    

    /** constructs a Server, its view and pingthread
     *   
    /** constructs a Server, its view and pingthread.
     *  
     */    
    public Server() {        
        //new PingThread(this).start();
    }
    
    public void createView() {
        try {
            this.view = new ServerTUIView(this);
            this.view.run();            
        } catch (IOException e1) {
            System.out.println("Could not create TUI vor server.");
            System.exit(0);
        }
    }
     
    public void sendChat(String[] inputSplit, String name) {        
        String result = Protocol.ProtServer.NOTIFYMESSAGE + " " + name + " ";
        
        for (int i = 1; i < inputSplit.length; i++) {
            result = result + inputSplit[i] + " ";
        }
        
        for (ClientHandler c: clientHandlerList) {
            c.send(result);
        }
    }
    
    /*
    //sends ping to all clients to test if each client is still connected    
    public void pingAll() {
        while (true) {
            for (ClientHandler c: clientHandlerList) {
                c.send("ping");
            }
            
            try { 
                this.currentThread().sleep(1000);
            } catch (InterruptedException e1) {
                sendToView("pinger interrupted.");
            }
        }
    }
    
    */
    
    public void leaveServer(ClientHandler client) {
        clientHandlerList.remove(client);
    }
    
    public void removeGame(Game game) {
        this.gameList.remove(game);
    }
    
    /**creates ServerSocket on input port.
     * 
     * @param input
     * @throws IOException     
     */
    
    //@ requires !this.running && Integer.parseInt(input) > 0;
    //@ ensures this.running && this.getServerSocket().isBound();
    public void startServer(String input) {
        if (this.running) {
            sendToView("Server already running, exit and restart to run server on different port.");
        } else {
            this.running = true;
            // parse input - the port
            int port = getPort(input);
            try {
                this.serverSocket = new ServerSocket(port);
                this.start();
            } catch (IOException e1) {
                sendToView("Could not create ServerSocket on port: " + port); 
                sendToView("Try again, note that port should not be in use and higher than 0.");
                this.running = false;
            }
        }
    }
    
    public void run() {
        accepter(); 
    }
    
    public void sendToView(String input) {
        if (this.view != null) {
            this.view.send(input);
        } 
    }    
    
    /**Notifies all clients that shutdown will happen, then exit the program and all its threads.
     * 
     */
    
    public void shutDown() {        
        this.running = false;
        if (this.view != null) {
            this.view.exit();
        }
        if (this.serverSocket != null) {
            try {
                this.serverSocket.close();
            } catch (IOException e) {
                sendToView("could not close serversocket");
            }
        }
    }    
    
    /** Returns the ServerSocket of this server.
     * 
     * @return ServerSocket
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
        while (this.running) {
    	    Socket sock = null;
    	    try {
    	        sock = this.serverSocket.accept();
    	        sendToView("New client connected!");
    	    } catch (IOException e1) {
    	        sendToView("Could not accept connection on serversocket.");
    	    }
    	    if (!this.serverSocket.isClosed()) {
        	    try {
        	        ClientHandler clientHandler = new ClientHandler(this, sock);
        	        this.clientHandlerList.add(clientHandler);
        	        new Thread(clientHandler).start();
        	    } catch (IOException e1) {
                    sendToView("Could not create client handler.");
                }
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
                sendToView("game " + i + " was joined");
                game = this.gameList.get(i);                
            }
            i++; //continue
        }
        
        //if no game found make a new one
        if (game == null) {
            sendToView("new game created");
            game = new Game(this); 
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
    
    /** Starts a Server-application by creating a new Server.
     *
     *
     */
    public static void main(String[] args) {
    	//create a new server
    	Server aServer = new Server();
    	aServer.createView();
    }

} // end of class Server

