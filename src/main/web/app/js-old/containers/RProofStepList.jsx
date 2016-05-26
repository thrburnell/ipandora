import { connect } from 'react-redux'
import JustifiedFormulaList from '../components/JustifiedFormulaList'
import { selectFormulaAsJustification } from '../actions'

const mapStateToProps = (state) => (
  {
    formulas:
      state.proofSteps.map(({ derived, justification }) => (
          {
            ...state.knownFormulas[derived],
            justification: justification.map((id) => state.knownFormulas[id].uiId)
          }
      )),
    clickable: state.proofStepState != 'AWAITING_VALIDITY_CHECK'
  }
)

const mapDispatchToProps = (dispatch) => (
  {
    onFormulaClick: (id) => dispatch(selectFormulaAsJustification(id))
  }
)

const RProofStepList = connect(
  mapStateToProps,
  mapDispatchToProps
)(JustifiedFormulaList)

export default RProofStepList

