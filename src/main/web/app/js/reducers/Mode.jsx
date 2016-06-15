import { TOGGLE_PROOF_MODE} from '../actions'
import { PROOF_MODE } from '../constants'

const Mode = (state="DIRECT", action) => {

  switch (action.type) {
    case TOGGLE_PROOF_MODE:
      return state == PROOF_MODE.INDUCTION
        ? PROOF_MODE.DIRECT
        : PROOF_MODE.INDUCTION

    default:
      return state
  }

}

export default Mode

