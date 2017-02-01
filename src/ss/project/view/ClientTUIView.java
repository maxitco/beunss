package ss.project.view;

import java.util.Observer;

import ss.project.Protocol;
import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Observable;
import ss.project.*;

public class ClientTUIView extends Terminal implements ClientView {
    
    private Client2 client;
    
    public ClientTUIView(Client2 client) throws IOException {
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
            } else if (inputSplit[0].equals("ai")) {
                send("Enter 'start <port>' to continue.");                
                this.client.setOnline(false);
            } else if (
                inputSplit[0].equals("start") && this.client.isOnline() 
                && inputSplit.length == 4
            ) {
                this.client.setPlayerName(inputSplit[1]);
                this.client.connectToServer(inputSplit[2], inputSplit[3]);
                send("connecting to server...");
            } else if (
                inputSplit[0].equals("start") && !this.client.isOnline() 
                && inputSplit.length == 2
            ) {
                this.client.connectToServer("localhost", inputSplit[1]);                
            } else if (inputSplit[0].equals("toggle ai")) {
                this.client.toggleAI(); 
            }
            
            else if (inputSplit[0].equals("restart")) {
                this.client.restart();
            } 
            
            else if (inputSplit[0].equals("exit")) {
                System.exit(0);
            } else if (
                inputSplit[0].equals("move") && inputSplit.length == 3 && this.client.isInGame()) {
                this.client.getServerHandler().send(
                        Protocol.Client.MAKEMOVE + " " + inputSplit[1] + " " + inputSplit[2]
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
        send("During the application you can always enter:\n"
                + "'toggle ai' to enable/disable the computer playing for you"
                + "'exit' to exit the application or \n"
                + "'restart' to restart the application\n\n");
        send(
            "Enter 'ai' to play against AI or "
            + "'multi' to play against other players"
        );
    } 
    
}
