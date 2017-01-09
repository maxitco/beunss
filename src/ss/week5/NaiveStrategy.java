package ss.week5;

import java.security.KeyStore.Entry;
import java.util.TreeSet;
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
        java.util.Set<Integer> Moves = new java.util.TreeSet<Integer>();
        for (int i = 0;i < Board.DIM*Board.DIM;i++) {
            if (b.isEmptyField(i)) {
                Moves.add(i);
            }
        }
        int next = (int) Math.random()*Moves.size() - 1;
        int count = 0;
        Iterator<Integer> setiterator = Moves.iterator();
        while (Moves.size() > 0 && setiterator.hasNext()) {
            if (next == count) {
                return setiterator.next().intValue();
            }
            count++;
        }
    }

}
