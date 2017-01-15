package ss.week6.voteMachine;
import java.util.*;

public class VoteMachine {
    private PartyList controllerPartyList;
    private VoteList controllerVoteList;
    private VoteView controllerView;
    
    public static void main(String[] args) {
        VoteMachine alpha = new VoteMachine();
        /*
        alpha.addParty("CDA");
        alpha.addParty("PVV");
        alpha.addParty("VVD");
        for(int i = 0; i<10; i++ ) {
            alpha.vote("CDA");
            alpha.vote("PVV");
            alpha.vote("PVV");
            alpha.vote("VVD");
            alpha.vote("VVD");
            alpha.vote("VVD");
        }        
        */
        alpha.start();
    }
    
    public VoteMachine() {
        controllerPartyList = new PartyList();
        controllerVoteList = new VoteList();
        controllerView = new ss.week6.voteMachine.gui.VoteGUIView(this);
        controllerVoteList.addObserver(controllerView);
        controllerPartyList.addObserver(controllerView);
    }
    
    public void addParty(String party) {
        if(!this.getParties().contains(party)) {
            this.controllerPartyList.addParty(party);
        } else {
            System.out.println("This was already added");
        }
    }
    
    public void vote(String party) {
        if (this.getParties().contains(party)) {
            this.controllerVoteList.addVote(party);
        } else {
            System.out.println("This party does not exsist");
        }
    }
    
    public void start() {
        controllerView.start();
    }
    
    public ArrayList<String> getParties() {
        return controllerPartyList.getParties();
    }
    
    public Map<String,Integer> getVotes() {
        return controllerVoteList.getVotes();
    }
    
    
}
