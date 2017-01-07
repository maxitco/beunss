package ss.week5;

import java.security.KeyStore.Entry;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.List;
import java.util.ArrayList;

public class NaiveStrategy implements Strategy {

    @Override
    public String getName() {
        return "Naive";
    }

    @Override
    public int determineMove(Board b, Mark m) {
        java.util.Set<Integer> Moves = new java.util.HashSet<Integer>();
        for (int i = 0;i < Board.DIM*Board.DIM;i++) {
            if (b.isEmptyField(i)) {
                Moves.add(i);
            }
        }
        Integer next = new Integer((int) Math.random()*Moves.size());
        int count = 0;
        while (Moves.size() > 0 && Moves.iterator().hasNext()) {
            if (next.equals(new Integer(count))) {
                Moves.iterator()
            }
            count++;
            /*if (b.isEmptyField(((Moves.get(next))) {
                return next;
            }*/
            
            Iterator<Integer> iteratorA = Moves.iterator();
            while(iteratorA.hasNext()) {
                int IntegerDieViaNextKomt = iteratorA.next(); //iteratorA.next is dus een integer, En zorgt ervoor dat telkens de volgende integer gepakt wordt
            }
        }
        
        return 0;
    }

}
