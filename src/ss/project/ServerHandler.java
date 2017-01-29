 package ss.project;

import java.io.IOException;
import java.net.Socket;

public class ServerHandler extends Terminal {
    private Client client;
    
    ServerHandler(Client inputClient, Socket inSock) throws IOException {
        super(inSock.getInputStream(), inSock.getOutputStream());
        this.client = inputClient;
    }
    
    @Override
    public void atStart() {
        //nada, wait for capabilities from server first
    }
    
    @Override
    public void handleInput(String input) {
      //split input around spaces
        String[] inputSplit = input.split(" ");
        
        if (inputSplit[0].equals(Protocol.Server.SERVERCAPABILITIES)) {
            //respond with capabilities of the client
            send(this.client.getCapabilities());
        } else if (inputSplit[0].equals(Protocol.Server.ASSIGNID)) {
            //set player ID
            try {
                int id = Integer.parseInt(inputSplit[1]);
                this.client.setPlayerId(id);
                //ask for more client input or notify waiting
                if (client.isOnline()) {
                    this.client.send("Connection established, waiting for other players"); 
                } else if (!client.isOnline()){
                    this.client.send("Enter AI difficulty 'easy'/'medium'/'hard'");
                }
            } catch (NumberFormatException e) {
                this.client.send("Server is sending rubbish, NumberFormatException");
            }                
        } else if (inputSplit[0].equals(Protocol.Server.STARTGAME)) {
            //notify the client that the game has started and create a board
            this.client.setInGame(true);
            this.client.send("Game has started");
            this.client.refreshBoard();
            this.client.send(this.client.getBoard().toString());
        } else if (inputSplit[0].equals(Protocol.Server.TURNOFPLAYER) && inputSplit.length == 2) {
            //notify the player whose turn it is
            try {
                //get the id of the current player
                int id = Integer.parseInt(inputSplit[1]);
                this.client.setCurrentTurnId(id);
                
                //compare current player to clientId to see who it is
                if (id == client.getPlayerId()) {
                    this.client.send("It is your turn, type: 'MOVE <x>, <y>' to make a move.");
                } else {
                    this.client.send("It is the turn of player " + inputSplit[1]);
                }                
            } catch (NumberFormatException e) {
                this.client.send("Server is sending rubbish, NumberFormatException");
            }            
        } else if (inputSplit[0].equals(Protocol.Server.NOTIFYMOVE) && inputSplit.length == 4) {
            //notify player of the move
            this.client.send(
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
                this.client.send(this.client.getBoard().toString());
                               
            } catch (NumberFormatException e) {
                this.client.send("Server is sending rubbish, NumberFormatException");
            }
        } else if (inputSplit[0].equals(Protocol.Server.NOTIFYEND) && inputSplit.length == 2) {
          //game has ended in a draw, notify client
            send("The game has ended in a draw, type EXIT to exit the game and start a new one"); 
            this.client.setInGame(false);
        } else if (
            //game has ended in win row or ended due to a disconnect
            inputSplit[0].equals(Protocol.Server.NOTIFYEND) && inputSplit.length == 3) {
            if(inputSplit[1].equals("1")) {
                this.client.send("Player " + inputSplit[2] + " has won.");
            } else {
                this.client.send("Player " + inputSplit[2] + " has disconnected.");
            }
            this.client.setInGame(false);
        } else {        
            send("Server is sending an unknown command");
        }
    }
}
