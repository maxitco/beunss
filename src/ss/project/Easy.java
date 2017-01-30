package ss.project;

import java.util.ArrayList;

public class Easy implements Difficulty {
    //private ArrayList<Field> Fields = ArrayList
    @Override
    public String getName() {
        return "easy";
    }
    
    //@ensures board.isReachableEmptyField(\result);
    @Override
    public Field determineMove(Board board, Mark m) {
        ArrayList<Field> moves = new ArrayList<Field>();
        for (int x = 0; x <= Board.MAXFIELD; x++) {
            for (int y = 0; y <= Board.MAXFIELD; y++) {
                Field empty = board.getEmptyField(x, y);
                if (empty != null) {
                    moves.add(empty);
                }
            }
        }
        return moves.get((int) (Math.random() * moves.size()));
    }

}