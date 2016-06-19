import { connect } from 'react-redux'
import BaseCase from '../components/BaseCase'
import { saveBaseInitialTerm, makeBaseProofStep } from '../actions'

const mapStateToProps = (state) => (
  {
    ...state.baseCase,
    active: state.toShow.valid
  }
)

const mapDispatchToProps = (dispatch) => (
  {
    onInitialEntry: (input) => dispatch(saveBaseInitialTerm(input)),
    onStepEntry: (input, justification) => dispatch(makeBaseProofStep(input, justification))
  }
)

const RBaseCase = connect(
  mapStateToProps,
  mapDispatchToProps
)(BaseCase)

export default RBaseCase

