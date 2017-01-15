package ss.week6.voteMachine;

import java.util.*;

public class VoteList extends Observable{
    Map<String, Integer> map; 
    
    public VoteList() {
        this.map = new HashMap<String, Integer>();
    }
    
    public void addVote(String party) {
        if (map.containsKey(party)) {
            Integer newValue = map.get(party) + 1;
            map.remove(party, map.get(party));
            map.put(party, newValue);
        } else {        
            map.put(party, 1);
        }
        setChanged();
        notifyObservers("vote");
    }
    
    public Map<String,Integer> getVotes() {
        return this.map;
    }
}
