package ss.week6.voteMachine;
import java.util.*;
public class VoteTUIView implements Observer, VoteView {
    private VoteMachine controller;
    
    public VoteTUIView(VoteMachine inController) {
        this.controller = inController;         
    }
    
    public void start() {
        System.out.println("pleas enter a command, enter 'HELP' to see al valid commands");
        Scanner scanner = new Scanner(System.in);
        
        while (scanner.hasNextLine()) {
            String line = scanner.nextLine();
            if (line.equals("VOTE")) {
                System.out.println("Enter a party to vote for it");
                String party = scanner.nextLine();
                controller.vote(party);
            } else if (line.equals("ADD PARTY")) {
                System.out.println("Enter the name of the party you want to add.");
                String addparty = scanner.nextLine();
                controller.addParty(addparty);
            } else if (line.equals("VOTES")) {
                showVotes(controller.getVotes());
            } else if (line.equals("PARTIES")) {
                showParties(controller.getParties());
            } else if (line.equals("EXIT")) {
                break;
            } else if (line.equals("HELP")) {
                System.out.println("The following are legit commands\n"
                        + "'VOTE':  to vote for a party\n"
                        + "'ADD PARTY': to add a new party\n" 
                        + "'VOTES': to view the amount of votes each party has\n"
                        + "'PARTIES': to view a list with all parties\n"
                        + "'EXIT': to exit the program");
            } else {
                showError("Error: nonvalid command, enter 'HELP' for help");
            }
            System.out.println("Task completed, you may enter a new command below");
        }
        scanner.close();
    }
    
    public void showVotes(Map<String,Integer> map) {
        Set<String> keyset = map.keySet();
        for(String key:keyset) {
            System.out.println("Party " + key + " has " + map.get(key).toString() + " votes."); 
        }
    }
    
    public void showParties(List<String> list) {
        System.out.println("Parties:"); 
        for(int i = 0; i<list.size(); i++) {
            System.out.println(list.get(i)); 
        }
    }
    
    public void showError(String input) {
        System.out.println(input);
    }
    
    public void update(Observable o, Object arg) {
        if (arg.equals("vote")) {
            System.out.println("Your vote has been submitted.");
        } else if (arg.equals("party")) {
            System.out.println("A party has been added.");
        } else {
            System.out.println("Error undefined action observed");
        }
    }
}
