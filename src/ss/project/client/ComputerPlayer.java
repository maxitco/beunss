package ss.project.client;

import ss.project.game.Board;
import ss.project.game.Field;
import ss.project.game.Mark;

public class ComputerPlayer implements Player {
    private Difficulty difficulty;
    
    public ComputerPlayer(Difficulty newdiff) {
        this.difficulty = newdiff;
    }
    @Override
    public String getName() {
        return this.difficulty.getName() + " Computer Player";
    }
    
    @Override
    public Field determineMove(Board board, Mark m) {
        return this.difficulty.determineMove(board, m);
    }

}
