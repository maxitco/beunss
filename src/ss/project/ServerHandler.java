package ss.project;

import java.io.IOException;
import java.net.Socket;

public class ServerHandler extends Terminal {
    private Client2 client;
    
    ServerHandler(Client2 inputClient, Socket inSock) throws IOException {
        super(inSock.getInputStream(), inSock.getOutputStream());
        this.client = inputClient;
    }
    
    @Override
    public void atStart() {
        //nada, wait for capabilities from server first
    }
    
    @Override
    public void send(String input) {
        super.send(input);
        System.out.println(input);
    }
    
    /**
     * handleInput() description
     * split input around spaces, and determine what action needs to be taken 
     * longer actions are placed in separate functions starting with "at"
     * these functions can be found below handleInput()
     */    
    
    @Override
    public void handleInput(String input) {
        System.out.println("server sends: " + input); //for testing
        //split input around spaces
        String[] inputSplit = input.split(" ");
        
        if (inputSplit[0].equals(Protocol.Server.SERVERCAPABILITIES)) {
            //respond with capabilities of the client
            send(this.client.getCapabilities());
        } else if (inputSplit[0].equals(Protocol.Server.ASSIGNID)) {
            atAssignId(inputSplit);                
        } else if (inputSplit[0].equals(Protocol.Server.STARTGAME)) {
            atStartGame(inputSplit);            
        } else if (inputSplit[0].equals(Protocol.Server.TURNOFPLAYER) && inputSplit.length == 2) {
            atTurnOfPlayer(inputSplit);                        
        } else if (inputSplit[0].equals(Protocol.Server.NOTIFYMOVE) && inputSplit.length == 4) {
            atNotifyMove(inputSplit);            
        } else if (inputSplit[0].equals(Protocol.Server.NOTIFYEND) 
            && inputSplit.length == 2 || inputSplit.length == 3
        ) {
            atNotifyEnd(inputSplit);          
        } else if (inputSplit[0].equals("error") && inputSplit.length == 2) {
            this.client.sendToView(Protocol.getError(inputSplit[1]));
        } else {        
            this.client.sendToView("Server is sending an unknown command");            
        }
    }
    
    /**
     * Start "at" functions belonging in handleInput 
     */
    
    public void atAssignId(String[] inputSplit) {
      //set player ID
        try {
            int id = Integer.parseInt(inputSplit[1]);
            this.client.setPlayerId(id);
            //ask for more client input or notify waiting
            if (client.isOnline()) {
                this.client.sendToView("Connection established, waiting for other players"); 
            } else if (!client.isOnline()) {
                this.client.sendToView("Enter AI difficulty 'easy'/'medium'/'hard'");
            }
        } catch (NumberFormatException e) {
            this.client.sendToView("Server is sending rubbish, NumberFormatException");
        }
    }
    
    public void atStartGame(String[] inputSplit) {
      //notify the client that the game has started and create a board
        this.client.setInGame(true);
        this.client.sendToView("Game has started");
        this.client.refreshBoard();
        this.client.sendToView(this.client.getBoard().toString());
    }
    
    public void atTurnOfPlayer(String[] inputSplit) {
      //notify the player whose turn it is
        try {
            //get the id of the current player
            int id = Integer.parseInt(inputSplit[1]);
            this.client.setCurrentTurnId(id);
            
            //compare current player to clientId to see who it is
            if (id == client.getPlayerId()) {
                this.client.sendToView("It is your turn, type: 'MOVE <x> <y>' to make a move.");
            } else {
                this.client.sendToView("It is the turn of player " + inputSplit[1]);
            }                
        } catch (NumberFormatException e) {
            this.client.sendToView("Server is sending rubbish, NumberFormatException");
        }
    }
    
    public void atNotifyMove(String[] inputSplit) {
      //notify player of the move
        this.client.sendToView(
            "Player " + inputSplit[1] 
            + " has made move x=" + inputSplit[2]
            + " y=" + inputSplit[3]
        );
        
        //try to add the move to the board, needs to have integers for x and y
        try {
            
            int id = Integer.parseInt(inputSplit[1]);
            int x = Integer.parseInt(inputSplit[2]);
            int y = Integer.parseInt(inputSplit[3]);
            
            //player is always displayed/playing as Mark.Black
            if (id == this.client.getPlayerId()) {
                this.client.getBoard().setField(x, y, Mark.Black);
            } else {
            //opponent is always displayed/playing as Mark.White
                this.client.getBoard().setField(x, y, Mark.White);
            }
            //print the current board
            this.client.sendToView(this.client.getBoard().toString());
                           
        } catch (NumberFormatException e) {
            this.client.sendToView("Server is sending rubbish, NumberFormatException");
        }        
    }
    
    public void atNotifyEnd(String[] inputSplit) {
        if (inputSplit.length == 2) {
            //game has ended in a draw, notify client
            send("The game has ended in a draw, "
                    + "type EXIT to exit the game and start a new one");          
        } else if (inputSplit.length == 3) {
            if (inputSplit[1].equals("1")) {
                this.client.sendToView("Player " + inputSplit[2] + " has won.");
            } else if (inputSplit[1].equals("3")) {
                this.client.sendToView("Player " + inputSplit[2] + " has disconnected.");
            } else {
                this.client.sendToView("Unknown game end condition");
            }            
        }
        this.client.setInGame(false);
    }
}

