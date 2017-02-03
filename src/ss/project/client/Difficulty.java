package ss.project.client;

import ss.project.game.Board;
import ss.project.game.Field;
import ss.project.game.Mark;

public interface Difficulty {
    public String getName();
    public Field determineMove(Board board, Mark m);
}
