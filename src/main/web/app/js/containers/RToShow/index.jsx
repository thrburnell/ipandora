import { connect } from 'react-redux'
import { getInductionSchema, toggleProofMode, validateToShow } from '../../actions'
import { PROOF_MODE } from '../../constants'
import ToShow from '../../components/ToShow'

const mapStateToProps = (state) => (
  {
    ...state.toShow,
    mode: state.mode
  }
)

const dispatchButtonClick = (formula, variable) => (
  (dispatch, getState) => {
    console.log(formula)

    switch (getState().mode) {
      case PROOF_MODE.INDUCTION:
        console.log("Induction not yet supported")
        return
      case PROOF_MODE.DIRECT:
        dispatch(validateToShow(formula))
        return
      default:
        console.log("Unknown proof mode...")
    }
  }
)

const mapDispatchToProps = (dispatch) => (
  {
    onToggleClick: () => dispatch(toggleProofMode()),
    onButtonClick: (formula, variable) => dispatch(dispatchButtonClick(formula, variable))
  }
)

const RToShow = connect(
  mapStateToProps,
  mapDispatchToProps
)(ToShow)

export default RToShow

