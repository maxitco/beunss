package ss.project.game;

import java.util.ArrayList;
import java.util.concurrent.locks.ReentrantLock;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.locks.Condition;

import ss.project.server.ClientHandler;
import ss.project.server.Server;


public class Game extends Thread {
    private ArrayList<ClientHandler> playerList = new ArrayList<ClientHandler>();
    private Board board;
    //answered is used for keeping track of client response, 
    //true to enter the while loop at the start
    private boolean answered = true; 
    private Lock lock = new ReentrantLock();
    private Condition notAnswered = lock.newCondition();
    private Server server;
    
    /*
     * counts at which turn the game is
     * starts at 0 since turnCounter++ is at the top of the while loop
     */
    private int turnCounter = 0; 
    
    
    public Game(Server inServer) {
        this.board = new Board();
        this.server = inServer;
    }
    

    //break game thread out of the waiting time to go to gameEnd
    //or if the game has not started remove dced client from playerList
    public void leaveGame(ClientHandler client) {
        if (this.isAlive()) {
            lock.lock();
            notAnswered.signal();
            lock.unlock();
        } else {
            this.playerList.remove(client);
        }        
    }
    
    public boolean isFull() {
        if (playerList.size() == 2) {
            return true;
        } else {
            return false;
        }
    }
    
    public synchronized void addPlayer(ClientHandler inputPlayer) {
        playerList.add(inputPlayer);
    }
    
    public ArrayList<ClientHandler> getPlayerList() {
        return this.playerList;
    }  
    
    //make move depending on input, player input is to identify who is trying to make a move
    public synchronized void makeMove(int x, int y, ClientHandler player) {
        //check if it is the turn of the player that calls the function
        
        if (!answered && playerList.get(whoseTurn()).equals(player)) {
            
            //make the move, mark depends on index in the array
            //0 --> black
            if (whoseTurn() == 0) {
                //try to make the move, if valid set answered true 
                if (board.setField(x, y, Mark.X)) {
                    notifyMove(x, y, player.getPlayerId());                    
                } else {
                    player.send("error 5"); //invalid --> return error 5 (invalid move)
                }
            //1 --> white
            } else {
              //try to make the move, if valid set answered true 
                if (board.setField(x, y, Mark.O)) {
                    notifyMove(x, y, player.getPlayerId());                    
                } else {
                    player.send("error 5"); //invalid --> return error 5 (invalid move)
                }                
            }

        } else {
            player.send("error 5"); //not his turn --> return error 5 (invalid move)
        }        
    }
    
    //notify all players which move was made
    public void notifyMove(int x, int y, int id) {
        lock.lock();
        for (ClientHandler c: this.playerList) {
            c.send(Protocol.ProtServer.NOTIFYMOVE + " " + id + " " + x + " " + y);
        }
        //set answered on true such that the game thread can continue
        this.answered = true;
        this.notAnswered.signal();
        lock.unlock();
    }
    
    //determine whose turn it is, depending on turn and amount of players
    public int whoseTurn() {
        return this.turnCounter % this.playerList.size();
    }
    
    //check if the game has ended
    public boolean gameEnd() {
        //check for disconnected players, then winner, then draw
        if (this.playerList.get(0).disconnected) {
            notifyEnd(this.playerList.get(0).getPlayerId(), 3);
            return true;
        } else if (this.playerList.get(1).disconnected) {
            notifyEnd(this.playerList.get(1).getPlayerId(), 3);
            return true;            
        } else if (this.board.isWinner(Mark.X)) {         
            notifyEnd(this.playerList.get(0).getPlayerId(), 1);   
            return true;
        } else if (this.board.isWinner(Mark.O)) {
            notifyEnd(this.playerList.get(1).getPlayerId(), 1);
            return true;
        //then check for draw
        } else if (this.turnCounter == 64) {
            notifyEnd();
            return true;
        }  else if (this.answered == false) {
            notifyEnd(this.playerList.get(whoseTurn()).getPlayerId(), 3);
            return true;
        }
        //do nothing if not ended
        return false;
    }
    
    //notify everyone who has won or who left the game.
    public void notifyEnd(int playerId, int reason) {
        if (reason == 1) {        
            for (ClientHandler c: this.playerList) {
                c.send(Protocol.ProtServer.NOTIFYEND + " 1 " + playerId);
                c.onFailure();
            } 
        } else if (reason == 3) {
            for (ClientHandler c: this.playerList) {
                c.send(Protocol.ProtServer.NOTIFYEND + " 3 " + playerId);
                c.onFailure();
            }  
        }
    }
    
    //notify everyone that the game has ended, draw
    public void notifyEnd() {
        for (ClientHandler c: this.playerList) {
            c.send(Protocol.ProtServer.NOTIFYEND + " 2");            
            c.onFailure();
        }  
    }
    
    @Override
    public void run() {
        lock.lock();
        //assign an id to each player (their index in the arrayList + 1)
        for (int i = 0; i < this.playerList.size(); i++) {
            int id = i + 1;
            this.playerList.get(i).setPlayerId(id);
            this.playerList.get(i).send(Protocol.ProtServer.ASSIGNID + " " + Integer.toString(id));
        }
        
        //notify players that the game has started   
        //includes game specifications and opponent info
        for (ClientHandler c: this.playerList) {
            c.send(
                    Protocol.ProtServer.STARTGAME 
                    + " 4|4|4|4 " 
                    + getPlayerList().get(0).getPlayerId()
                    + "|" + getPlayerList().get(0).getPlayerName()
                    + "|" + "0000ff"
                    + " "
                    + getPlayerList().get(1).getPlayerId()
                    + "|" + getPlayerList().get(1).getPlayerName()
                    + "|" + "ff0000" 
            );          
        }      
                        
        while (!gameEnd()) {     
            this.turnCounter++; //next turn, at top of loop such that not updated when game is ended
            for (ClientHandler c: this.playerList) {
                c.send(
                    Protocol.ProtServer.TURNOFPLAYER + " " 
                    + Integer.toString(playerList.get(whoseTurn()).getPlayerId())
                );          
            }
            //set answered on false, is set true when the player whose turn it is makes a move
            this.answered = false;
            //wait until signaled (when an answer was submitted), or timeout after 20 seconds            
            try {
                this.notAnswered.await(120, TimeUnit.SECONDS);                
            } catch (InterruptedException e) {
                for (ClientHandler c: this.playerList) {
                    c.send(
                        "Game interrupted."
                    );          
                }
            }                            
        }
        
        this.server.removeGame(this);
        lock.unlock();
    }
}
