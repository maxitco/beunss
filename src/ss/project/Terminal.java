package ss.project;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;

public class Terminal {
    private final BufferedReader in;
        
    public Terminal() throws IOException {
        this.in = new BufferedReader(new InputStreamReader(System.in));        
    } 
    
    public void write() {
        String line = null; 
        System.out.println("type here: ");
        try { 
            
            //continuously read input and print it
            while (true) { 
                while ((line = in.readLine()) != null) {
                    handle(line);
                }
            } 
        } catch (IOException e) { 
            System.out.println("Something went wrong reading from socket"); 
        } 
    }
    
    public void handle(String input) {
        System.out.println(input);
        System.out.println("type here: ");
    }
}
