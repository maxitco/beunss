package ss.project.view;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.InputStream;
import java.io.OutputStream;


public class Terminal {
    private final BufferedReader in;
    private final BufferedWriter out;
    private boolean exit = false;
        
    public Terminal(InputStream in, OutputStream out) throws IOException {
        this.in = new BufferedReader(new InputStreamReader(in)); 
        this.out = new BufferedWriter(new OutputStreamWriter(out)); 
    } 
    
    public void atStart() {
        send("terminal started");
    }
    
    public void run() {
        
        atStart();        
        try {        
            String line = in.readLine(); 
            //continuously read input and print it
            while (line != null && !exit) {
                handleInput(line);
                line = in.readLine();
            }             
        } catch (IOException e) { 
            send("error 4"); 
        } 
    }
    
    //send String to out
    public void send(String input) {
        try {
            out.write(input);
            out.newLine();
            out.flush();
        } catch (IOException e) { 
            onFailure();
        } 
    }
    
    public void handleInput(String input) {
        send(input);        
    }
    
    public void onFailure() {
        System.out.println("Something went wrong with sending through socket");
    }
    
    public void exit() {
        this.exit = true;
    }
}
