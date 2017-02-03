package ss.project;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

public class Hard implements Difficulty {

	@Override
	public String getName() {
		return "hard";
	}

	@Override
	public Field determineMove(Board board, Mark m) {
		
        ArrayList<Field> moves = this.getMoves(board);
        Map<Field, Integer> result = this.getResultMap(board, m);
        
        //Choose candidate with highest potential score
        int maxValue = Collections.max(result.values());
        Iterator<Map.Entry<Field, Integer>> it = result.entrySet().iterator();
        while (it.hasNext()) {
        	Map.Entry<Field,Integer> item = it.next();
        	if (item.getValue().intValue() < maxValue) {
        		it.remove();
        	}
        }
        it = result.entrySet().iterator();
        int next = (int) (Math.random() * new Double(result.size()));
        int count = 0;
        while (it.hasNext()) {
        	Map.Entry<Field,Integer> item = it.next();
        	if (count == next) {
        		return item.getKey();
        	}
        	count++;
        }
        
        return null;
	}
	//@requires board != null;
	public ArrayList<Field> getMoves(Board board) {
		ArrayList<Field> moves = new ArrayList<Field>();
        for (int x = 0; x <= Board.MAXFIELD; x++) {
            for (int y = 0; y <= Board.MAXFIELD; y++) {
                Field empty = board.getEmptyField(x, y);
                if (empty != null) {
                    moves.add(empty);
                }
            }
        }
        return moves;
	}
	//@requires board != null;
	//@requires m != null;
	public int getFutureImpact(Board board, Mark m) {
		int result = 0;
		ArrayList<Field> moves = this.getMoves(board);
		for (Field field : moves) {
			Board myboard = board.copy();
			Board enemboard = board.copy();
			myboard.setField(field, m);
			enemboard.setField(field, m.other());
			if (myboard.isWinner(m)) {
				result += 50;
			}
			else if (enemboard.isWinner(m.other())) {
				result -= 50;
			}
		}
		return result;
	}
	
	public Map<Field, Integer> getResultMap(Board board, Mark m) {
		Map<Field, Integer> result = new HashMap<Field, Integer>();
		ArrayList<Field> moves = this.getMoves(board);
		for (Field field : moves) {
			Board myboard = board.copy();
			Board enemboard = board.copy();
			myboard.setField(field, m);
			enemboard.setField(field, m.other());
			if (myboard.isWinner(m)) {
				result.put(field, new Integer(500));
			}
			else if (enemboard.isWinner(m.other())) {
				result.put(field, new Integer(100));
			}
			else {
				result.put(field, new Integer(countSurroundings(field, board, m) + getFutureImpact(myboard, m)));
			}
			//result.put(field, result.get(field) + getFutureImpact(myboard, m));
		}

		return result;
	}
	
	public int countSurroundings(Field field, Board board, Mark m) {
    	int result = 0;
    	for (int z = -1; z <= 1; z++) {
    		for (int i = -1; i <= 1; i++) {
    			for (int a = -1; a <= 1; a++) {
    				Field neighbour = board.walkField(field, i, a, z);
    				//next to field of same color
    				if (neighbour != null) {
    					Mark nextmark = board.getMark(neighbour);
    					if (nextmark != null && nextmark.equals(m)) {
        					result ++;
    					}
    				}
    				//next to boundary
    				else if (neighbour == null) {
    					result++;
    				}
    			}
    		}
    	}
    	return result;
    }

}
