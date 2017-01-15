package ss.week6.voteMachine;
import java.util.*;
public class PartyList extends Observable {
    private ArrayList<String> partyList;
    
    public PartyList () {
        partyList = new ArrayList<String>();    
    }
    
    public void addParty(String input) {
        partyList.add(input);    
        setChanged();
        notifyObservers("party");
    }
    
    public boolean hasParty(String input) {
        return partyList.contains(input);
    }
    
    public ArrayList<String> getParties() {
        return partyList;
    }
}
