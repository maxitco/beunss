package ss.project;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;
import ss.project.view.*;
 
public class Client2 {
    private Socket sock;
    private String playerName;
    private int playerId;
    private Board board;
    private ServerHandler serverHandler;
    private boolean online;
    private boolean inGame = false;
    private int currentTurnId;
    private ss.project.view.ClientView view;  
    private boolean aiEnabled = false;
    private Player hardAI = new ComputerPlayer(new Hard());
    
    public Client2() throws IOException {
        this.playerName = "NoNamePepe";     //should be overwritten 
        this.view = new ClientTUIView(this);
        this.view.run();
    }
    
    public void toggleAI() {
        this.aiEnabled = !this.aiEnabled;
        if (this.aiEnabled) {
            sendToView("AI is now on");
        } else {
            sendToView("AI is now off");
        }
    }
    
    public String hint() {
        if (inGame && this.currentTurnId == this.playerId) {
            Field field = this.hardAI.determineMove(this.board, Mark.Black);
            return "move(x y): " + field.getMove();
        }  else {
            return "hing is only available when it is your turn in game.";
        }
    }
    
    /*
     * ServerHandler functions
     */
    
    public void atTurnOfPlayer(String[] inputSplit) {
        //notify the player whose turn it is
          try {
              //get the id of the current player
              int id = Integer.parseInt(inputSplit[1]);
              setCurrentTurnId(id);
              
              //compare current player to clientId to see who it is
              if (id == getPlayerId()) {
                  sendToView("It is your turn, type: 'move <x> <y>' to make a move.");
                  //let the AI make a move for you
                  if (this.aiEnabled) {
                      Field field = this.hardAI.determineMove(board, Mark.Black);
                      sendToServer(Protocol.Client.MAKEMOVE + " " + field.getMove());
                  }
              } else {
                  sendToView("It is the turn of player " + inputSplit[1]);
              }                
          } catch (NumberFormatException e) {
              sendToView("Server is sending rubbish, NumberFormatException");
          }
      }
    
    public void setOnline(boolean input) {
        this.online = input;
    }
    
    /*@ pure */ public ServerHandler getServerHandler() {
        return this.serverHandler;
    } 
      
    public void refreshBoard() {
        this.board = new Board();
    }
    
    public void setPlayerName(String input) {
        this.playerName = input;        
    }
    
    public void setPlayerId(int input) {
        this.playerId = input;
    }
    
    public void setCurrentTurnId(int input) {
        this.currentTurnId = input;
    }
    
    public int getCurrentTurnId() {
        return this.currentTurnId;
    }
    
    public void setInGame(boolean input) {
        this.inGame = input;
    }
    
    /*@ pure */ public String getPlayerName() {
        return this.playerName;
    }  
    
    /*@ pure */ public int getPlayerId() {
        return this.playerId;
    }  
    
    /*@ pure */ public Board getBoard() {
        return this.board;
    }  
    
    /*@ pure */ public boolean isOnline() {
        return this.online;
    }
    
    /*@ pure */ public boolean isInGame() {
        return this.inGame;
    }
    
    /*@ pure */ public String getCapabilities() {
        return Protocol.Client.SENDCAPABILITIES + " 2 " + this.playerName + " 0 4 4 4 4 0 0";
    }
    
    public void sendToServer(String input) {
        this.serverHandler.send(input);
    }
    
    public void sendToView(String input) {
        this.view.send(input);
    }
    
    public void connectToServer(String ip, String socket) {
        InetAddress addr = null;
        Socket sock = null;
        int port = Server.getPort(socket);
        
        // check args[1] - the IP-adress
        try {
            addr = InetAddress.getByName(ip);
        } catch (UnknownHostException e) {
            sendToView("ERROR: host " + ip + " unknown."); 
            sendToView("try again");
        }
        
        // try to open a Socket 
        try {
            sock = new Socket(addr, port);
            this.serverHandler = new ServerHandler(this, sock);
            this.serverHandler.start();
            sendToView("setting up game...");
        } catch (IOException e) {
            sendToView("ERROR: could not create a socket on " + addr
                    + " and port " + port);            
            sendToView("try again");
        }        
    }
    
    //resets the client
    public void restart() {
        sendToView("\n\nRestarting...");
        if(this.serverHandler != null) {
            this.serverHandler.exit();
        }
        this.inGame = false;
        this.view.atStart();        
    }
    
    /** Starts a Client application. */
    public static void main(String[] args) {
        //construct a client
        try {
            Client2 aClient = new Client2();
        } catch(IOException e1) {
            System.out.println("could not construct view");
            System.exit(0);
        }
    }
}
