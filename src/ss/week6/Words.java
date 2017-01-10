package ss.week6;

import java.util.Scanner;

public class Words {
    public static void main(String[] args) {
        
        
        Scanner inputScanner = new Scanner(System.in);
        String input = "notempty";
        System.out.println("Enter a sentence. \n");
        System.out.print("Line (or 'end'): ");
        while (inputScanner.hasNext()) {
            input = inputScanner.nextLine();
            String[] inputSplit = input.split(" ");
            
            if (inputSplit[0].equals("end")) {
                break;
            } else {
                
                for(Integer i = 1; i <= inputSplit.length; i++) {
                    System.out.println("Word ".concat((i.toString().concat(": ")).concat(inputSplit[i-1])));
                }
            }
            System.out.print("\nLine (or 'end'): ");
            
        }
        System.out.println("End of program." );
        inputScanner.close();
    }    
    
}
