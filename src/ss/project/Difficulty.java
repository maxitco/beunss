package ss.project;

public interface Difficulty {
    public String getName();
    public Field determineMove(Board board);
}
