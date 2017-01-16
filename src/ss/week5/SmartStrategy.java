package ss.week5;

import java.security.KeyStore.Entry;
import java.util.TreeSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.List;
import java.util.ArrayList;

public class SmartStrategy implements Strategy {

    @Override
    public String getName() {
        return "Smart";
    }

    @Override
    public int determineMove(Board b, Mark m) {
        //Collect set of empty fields
        java.util.Set<Integer> Moves = new java.util.TreeSet<Integer>();
        for (int i = 0;i < Board.DIM*Board.DIM;i++) {
            if (b.isEmptyField(i)) {
                Moves.add(i);
            }
        }
        for(Integer field : Moves ) {
            //if field for direct win, select that field
            Board playfield = b.deepCopy();
            playfield.setField(field.intValue(), m);
            if (playfield.isWinner(m)) {
                return field.intValue();
            }
            //if field for opponent win, select that field
            playfield = b.deepCopy();
            playfield.setField(field.intValue(), m.other());
            if (playfield.isWinner(m.other())) {
                return field.intValue();
            }   
        }
        //if middle field empty: select that field
        int middle = Board.DIM*Board.DIM/2;
        if (b.isEmptyField(middle)) {
            return middle;
        }
        //else select random field
        int next = new java.util.Random().nextInt(Moves.size() - 1);
        int count = 0;
        for(Integer field : Moves ) {
            if (next == count) {
                return field.intValue();
            }
            count++;
        }
        //Strategy fail
        return -1;
    }
}
