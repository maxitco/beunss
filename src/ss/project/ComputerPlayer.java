package ss.project;

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
