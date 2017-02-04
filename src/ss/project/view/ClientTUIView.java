package ss.project.view;

import ss.project.client.Client;
import ss.project.game.Protocol;


import java.io.IOException;

public class ClientTUIView extends Terminal implements ClientView {
    
    private Client client;
    
    public ClientTUIView(Client client) throws IOException {
        super(System.in, System.out);        
        this.client = client;         
    }
    
    public void showBoard() {
        send(this.client.getBoard().toString());        
    }  

    @Override
    public void handleInput(String input) {
        if (input != null) {
            
            //split input around spaces
            String[] inputSplit = input.split(" ");
            
            if (inputSplit[0].equals("multi")) {
                send("Enter 'start <playername> <server ip> <port>' to continue.");     
                this.client.setOnline(true);
            } else if (inputSplit[0].equals(Protocol.ProtClient.SENDMESSAGE)) {
                this.client.sendToServer(input);
            } else if (inputSplit[0].equals("ai") && inputSplit.length == 1) {
                send("Enter 'start <port> <ai difficulty ('easy'/'medium'/'hard')>' to continue.");
                this.client.setOnline(false);
            } else if (
                inputSplit[0].equals("start") && this.client.isOnline() 
                && inputSplit.length == 4
            ) {
                send("connecting to server...");
                this.client.setPlayerName(inputSplit[1]);
                this.client.connectToServer(inputSplit[2], inputSplit[3]);                
            } else if (
                inputSplit[0].equals("start") && !this.client.isOnline() 
                && inputSplit.length == 3
            ) {
                this.client.atAI(inputSplit);
                this.client.connectToServer("localhost", inputSplit[1]);                
            } else if (inputSplit[0].equals("aitoggle")) {
                if(this.client.toggleAI()) {
                    this.client.sendToView("ai is now on");
                } else {
                    this.client.sendToView("ai is now off");
                } 
            } else if (inputSplit[0].equals("hint")) {
                send(this.client.hint());
            }  
            
            else if (inputSplit[0].equals("restart")) {
                this.client.restart();
            } 
            
            else if (inputSplit[0].equals("exit")) {
                System.exit(0);
            } else if (
                inputSplit[0].equals("move") && inputSplit.length == 3 && this.client.isInGame()) {
                this.client.getServerHandler().send(
                        Protocol.ProtClient.MAKEMOVE + " " + inputSplit[1] + " " + inputSplit[2]
                );
            } else {
                send(
                    "You entered: '" + input 
                    + "' which is not valid input or can only be done if it is your turn in the game."                    
                );
                
                if (this.client.isInGame()) {
                    if (this.client.getCurrentTurnId() != this.client.getPlayerId()) {
                        send("Note that it is not your turn now");
                    }
                } else {
                    send("Note that you are not in game right now");
                }          
            }
        } else {
            send("null input, y u do this?");
        }
    }
    
    
    @Override
    public void atStart() {
        send("During the application you can enter:\n"
                + "'sendMessage <message>' to chat"
                + "'hint' when in game to get a move suggested"
                + "'aitoggle' to enable/disable the computer playing for you"
                + "'exit' to exit the application or \n"
                + "'restart' to restart the application\n\n");
        send(
            "Enter 'ai' to play against AI or "
            + "'multi' to play against other players"
        );
    } 
    
}
