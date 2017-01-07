package ss.week5;

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
        while (Moves.size() > 0) {
            Integer next = new Integer((int) Math.random()*Moves.size());
            /*if (b.isEmptyField(((Moves.get(next))) {
                return next;
            }*/
        }
        
        return 0;
    }

}
