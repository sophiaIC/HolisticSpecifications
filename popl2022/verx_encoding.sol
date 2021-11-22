contract Crowdsale {
    Escrow escrow;
    uint256 closeTime;
    uint256 raised = 0;
    uint256 goal = 10000 * 10**18;

    function constructor() {
        escrow = new Escrow(0x1234);
        closeTime = now + 20 days;
    }

    function invest() payable {
        require (raised < goal);
        require (now <= closeTime);
        escrow.deposit.value(msg.value)(msg.sender);
        raised += msg.value;
    }

    function close() {
        require (now > closeTime || raised >= goal);
        if (raised >= goal) {
            escrow.close();
        } else {
            escrow.refund();
        }
    }
}

contract Escrow {
    address owner, beneficiary;
    mapping (address => uint256) deposits;
    enum State (OPEN, SUCCESS, WITHDRAWN, REFUNDABLE, REFUNDED);
    State state = OPEN;

    constructor (address b) {
        owner = msg.sender;
        beneficiary = b;
    }
    modifier onlyOwner {
        require (msg.sender == owner);
    }
    modifier onlyThis {
        require (msg.sender == this);
    }
    function close() onlyOwner {state = SUCCESS;}
    function setRefundable() onlyOwner {state = REFUNDABLE;}
    function setRefunded() onlyThis {state = REFUNDED;}
    function setWithdrawn() onlyThis {state = WITHDRAWN;}
    function deposit(address p) onlyOwner payable {
        deposits[p] = deposits[p] + msg.value;
    }
    function withdraw(){
        require(state == SUCCESS);
        this.setWithdrawn();
        beneficiary.transfer(this.balance);
    }
    function claimRefund(address p){
        require(state == REFUNDABLE);
        uint256 amount = this.deposits[p];
        this.setRefunded();
        this.deposits[p] = 0;
        p.call.value(amount)();
    }
}
