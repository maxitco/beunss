package ss.project.client;

import java.io.IOException;
import java.net.InetAddress;
import java.net.Socket;
import java.net.UnknownHostException;
import java.util.Observable;
import java.util.Observer;

import ss.project.game.Protocol;
import ss.project.game.Board;
import ss.project.game.Field;
import ss.project.game.Mark;
import ss.project.server.Server;
import ss.project.view.ClientView;
import ss.project.view.ClientTUIView;
 

public class Client implements Observer {    
    private String playerName;    
    private String opponentName;
    private int playerId;
    private int currentTurnId;
    private boolean online;
    private boolean inGame = false;
    private boolean aiEnabled = false;      
    private Board board;
    private ServerHandler serverHandler;
    private ClientView view;  
    private ComputerPlayer ai = new ComputerPlayer(new Hard());

    public boolean canChat;

    //set standard name for AI
    //view creation is not done in constructor, as for AI clients it is not desired
    public Client() {
        this.playerName = "NoNamePepeAI";     
    }

    //creates a view for the client
    public void createNewView() {
        try {
            this.view = new ClientTUIView(this);
            this.view.run();
        } catch (IOException e1) {
            System.out.println("could not create view");
            System.exit(0);
        }       
    }
    
    public void update(Observable obs, Object obj) {
        if(this.view != null && obj.equals("boardchanged")) {
            this.view.showBoard();
        }
    }

    //set functions
    public void setOnline(boolean input) {
        this.online = input;
    }

    public void setPlayerName(String input) {
        this.playerName = input;        
    }   

    public void setAI(ComputerPlayer player) {
        this.ai = player;
        this.playerName = player.getName();
    }

    public void setInGame(boolean input) {
        this.inGame = input;
    }

    //get, is and toggle functions
    /*@ pure */ public ServerHandler getServerHandler() {
        return this.serverHandler;
    } 

    public int getCurrentTurnId() {
        return this.currentTurnId;
    }

    /*@ pure */ public int getPlayerId() {
        return this.playerId;
    }  

    /*@ pure */ public Board getBoard() {
        return this.board;
    }  

    /*@ pure */ public String getCapabilities() {
        return Protocol.ProtClient.SENDCAPABILITIES + " 2 " + this.playerName + " 0 4 4 4 4 1 0";
    }

    /*@ pure */ public boolean isOnline() {
        return this.online;
    }

    /*@ pure */ public boolean isInGame() {
        return this.inGame;
    }    

    public boolean toggleAI() {
        this.aiEnabled = !this.aiEnabled;
        return aiEnabled;
    }    

    //at functions, linked to serverHandler
    public void atAI(String[] inputSplit) {
        Client client = new Client();
        if (inputSplit[2].equals("easy")) {            
            client.setAI(new ComputerPlayer(new Easy()));
        } else if (inputSplit[2].equals("medium")) {
            client.setAI(new ComputerPlayer(new Medium()));
        } else if (inputSplit[2].equals("hard")) {
            client.setAI(new ComputerPlayer(new Hard()));
        }
        //turn the ai on
        client.toggleAI();
        client.connectToServer("localhost", inputSplit[1]);
    }

    public void atTurnOfPlayer(String[] inputSplit) {
        //notify the player whose turn it is
        try {
            //get the id of the current player
            this.currentTurnId = Integer.parseInt(inputSplit[1]);            

            //compare current player to clientId to see who it is
            if (this.currentTurnId == getPlayerId()) {
                sendToView("It is your turn, type: 'move <x> <y>' to make a move.");
                //let the AI make a move for you
                if (this.aiEnabled) {
                    Field field = this.ai.determineMove(board, Mark.X);
                    sendToServer(Protocol.ProtClient.MAKEMOVE + " " + field.getMove());
                }
            } else {
                sendToView("It is the turn of player " + this.opponentName);
            }                
        } catch (NumberFormatException e) {
            sendToView("Server is sending rubbish, NumberFormatException");
        }
    }

    public void atAssignId(String[] inputSplit) {
        //set player ID
        try {
            this.playerId = Integer.parseInt(inputSplit[1]);              
            //ask for more client input or notify waiting
            if (isOnline()) {
                sendToView("Connection established, waiting for other players"); 
            } else if (!isOnline()) {
                sendToView("Enter AI difficulty 'easy'/'medium'/'hard'");
            }
        } catch (NumberFormatException e) {
            sendToView("Server is sending rubbish, NumberFormatException");
        }
    }

    public void atStartGame(String[] inputSplit) {
        //notify the client that the game has started and create a board
        this.inGame = true;
        sendToView("Game has started");
        refreshBoard();        
        sendToView(this.board.toString());

        //set opponent name as name of player with not this id
        String[] inputSplit2 = inputSplit[2].split("\\|");
        String[] inputSplit3 = inputSplit[3].split("\\|");
        if (
                Integer.parseInt(inputSplit2[0]) == this.playerId 
                && inputSplit3.length > 1
                ) {
            opponentName = inputSplit3[1];
        } else if (
                Integer.parseInt(inputSplit3[0]) == this.playerId 
                && inputSplit2.length > 1
                ) {
            opponentName = inputSplit2[1];
        } else {
            sendToView("Could not obtain opponent playername from game start.");
        }
    }



    public void atNotifyMove(String[] inputSplit) {
        //notify player of the move
        if (this.serverHandler.isYou(inputSplit[1])) {
            sendToView(
                    "You made move x=" + inputSplit[2]
                            + " y=" + inputSplit[3]
                    );
        } else {
            sendToView(
                    this.opponentName + " made move x=" + inputSplit[2]
                            + " y=" + inputSplit[3]
                    );
        }        

        //try to add the move to the board, needs to have integers for x and y
        try {

            int id = Integer.parseInt(inputSplit[1]);
            int x = Integer.parseInt(inputSplit[2]);
            int y = Integer.parseInt(inputSplit[3]);

            //player is always displayed/playing as Mark.Black
            if (id == this.playerId) {
                this.board.setField(x, y, Mark.X);
            } else {
                //opponent is always displayed/playing as Mark.White
                this.board.setField(x, y, Mark.O);
            }    

        } catch (NumberFormatException e) {
            sendToView("Server is sending rubbish, NumberFormatException");
        }        
    }

    public void atNotifyEnd(String[] inputSplit) {
        if (inputSplit.length == 2) {
            //game has ended in a draw, notify client
            this.serverHandler.send("The game has ended in a draw, "
                    + "type EXIT to exit the game and start a new one");          
        } else if (inputSplit.length == 3) {
            if (inputSplit[1].equals("1")) {
                if (this.serverHandler.isYou(inputSplit[2])) {
                    sendToView("You have won.");
                } else {
                    sendToView("Player " + this.opponentName + " has won.");
                }

            } else if (inputSplit[1].equals("3")) {
                sendToView("Player " + this.opponentName + " has disconnected.");
            } else {
                sendToView("Unknown game end condition");
            }            
        }
        this.inGame = false;
    }

    public void atNotifyMessage(String[] inputSplit) {
        String result = inputSplit[1] + ": ";

        for (int i = 2; i < inputSplit.length; i++) {
            result = result + inputSplit[i] + " ";
        }
        sendToView(result);
    }

    public String hint() {
        if (inGame && this.currentTurnId == this.playerId) {
            Field field = this.ai.determineMove(this.board, Mark.X);
            return "move(x y): " + field.getMove();
        }  else {
            return "Hint is only available when it is your turn in game.";
        }
    }

    public void sendToServer(String input) {
        if (this.serverHandler != null) {
            this.serverHandler.send(input);
        } else {
            sendToView("Error connection to server is required for this action.");
        }
    }

    public void sendToView(String input) {
        if (this.view != null) {
            this.view.send(input);
        }
    }

    public void connectToServer(String ip, String socketPort) {
        InetAddress addr = null;

        int port = Server.getPort(socketPort);

        // check args[1] - the IP-adress
        try {
            addr = InetAddress.getByName(ip);
        } catch (UnknownHostException e) {
            sendToView("ERROR: host " + ip + " unknown."); 
            sendToView("try again");
        }

        // try to open a Socket 
        try {
            Socket sock = new Socket(addr, port);
            this.serverHandler = new ServerHandler(this, sock);
            new Thread(this.serverHandler).start();
            sendToView("setting up game...");
        } catch (IOException e) {
            sendToView("ERROR: could not create a socket on " + addr
                    + " and port " + port);            
            sendToView("try again");
        }        
    }

    public void refreshBoard() {
        this.board = new Board();
        this.board.addObserver(this);
    }


    //resets the client
    public void restart() {
        sendToView("\n\nRestarting...");
        if (this.serverHandler != null) {
            this.serverHandler.exit();
        }
        this.inGame = false;
        this.view.atStart();        
    }

    /** Starts a Client application. */
    public static void main(String[] args) {
        //construct a client
        Client aClient = new Client();
        aClient.createNewView();        
    }
}
