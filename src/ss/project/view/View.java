package ss.project.view;

import java.util.Observer;

public interface View {
    public void run();    
    public void atStart();
    public void handleInput(String input);
    public void send(String inpt);
    public void exit();
}
